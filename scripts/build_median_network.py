"""Derive bounded median-only SIMD networks from footprint and rank declarations."""

from pathlib import Path

MAX_WINDOW_VOLUME = 128


def supported_windows(max_volume: int = MAX_WINDOW_VOLUME) -> tuple[int, ...]:
    """Derive odd three-dimensional footprints within the code-size budget."""
    return tuple(size for size in range(3, max_volume + 1, 2) if size**3 <= max_volume)


def network_source(window: int) -> str:
    """Prune a bitonic network to the selected median, simplifying padded infinity."""
    volume = window**3
    rank = volume // 2
    capacity = 1 << (volume - 1).bit_length()
    nodes = [("input", index) for index in range(volume)] + [("inf",)]
    infinity = volume
    wires = list(range(volume)) + [infinity] * (capacity - volume)
    for stage in range(1, capacity.bit_length()):
        span = 1 << stage
        distance = span >> 1
        while distance:
            for index in range(capacity):
                partner = index ^ distance
                if partner <= index:
                    continue
                left, right = wires[index], wires[partner]
                if left == infinity or right == infinity:
                    low = right if left == infinity else left
                    high = infinity
                else:
                    low = len(nodes)
                    nodes.append(("min", left, right))
                    high = len(nodes)
                    nodes.append(("max", left, right))
                wires[index], wires[partner] = (
                    (low, high) if index & span == 0 else (high, low)
                )
            distance >>= 1
    required = set()
    pending = [wires[rank]]
    while pending:
        node = pending.pop()
        if node in required:
            continue
        required.add(node)
        if nodes[node][0] in ("min", "max"):
            pending.extend(nodes[node][1:])
    lines = [
        '__attribute__((target("avx2"), noinline))',
        f"static void median_network_{window}(const float* input, float* output,",
        "std::size_t depth, std::size_t height, std::size_t width,",
        "std::size_t padded_height, std::size_t padded_width, std::size_t output_width) {",
        "for (std::size_t z=0; z<depth; ++z) {",
        "for (std::size_t y=0; y<height; ++y) {",
        "for (std::size_t x=0; x<width; x+=8) {",
        "const float* base=input+(z*padded_height+y)*padded_width+x;",
    ]
    loaded = set()
    for node in sorted(required):
        if nodes[node][0] not in ("min", "max"):
            continue
        operation, left, right = nodes[node]
        for parent in (left, right):
            if nodes[parent][0] == "input" and parent not in loaded:
                position = nodes[parent][1]
                dz = position // (window * window)
                dy = (position // window) % window
                dx = position % window
                lines.append(
                    f"const __m256 v{parent}=_mm256_loadu_ps(base+"
                    f"{dz}*padded_height*padded_width+{dy}*padded_width+{dx});"
                )
                loaded.add(parent)
        lines.append(
            f"const __m256 v{node}=_mm256_{operation}_ps(v{left},v{right});"
        )
    lines.append(
        f"_mm256_storeu_ps(output+(z*height+y)*output_width+x,v{wires[rank]});"
    )
    lines.extend(["}", "}", "}", "}"])
    return "\n".join(lines)


def build_median_network_header(destination: Path) -> None:
    """Write deterministic generated source; no compiler runs at import/runtime."""
    windows = supported_windows()
    source = ["// Generated from the bounded footprint/rank network declaration.",
              "static constexpr int median_windows[] = {" + ",".join(map(str, windows)) + "};",
              "#if OPENHCS_MEDIAN_AVX2"]
    source.extend(network_source(window) for window in windows)
    source.extend([
        "static void run_median_network(int window, const float* input, float* output,",
        "std::size_t depth, std::size_t height, std::size_t width,",
        "std::size_t padded_height, std::size_t padded_width, std::size_t output_width) {",
        "switch (window) {",
    ])
    source.extend(
        f"case {window}: median_network_{window}(input,output,depth,height,width,"
        "padded_height,padded_width,output_width); break;" for window in windows
    )
    source.extend(["}", "}", "#endif", ""])
    destination.parent.mkdir(parents=True, exist_ok=True)
    destination.write_text("\n".join(source), encoding="utf-8")
