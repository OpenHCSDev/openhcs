"""Noise2Void (N2V2) inference as an OpenHCS custom function: model file plus images in, images out.

The model file is the one ``n2v2_fit`` (neighbouring file) writes. Inference has
no random step, so the same model file and the same images give the same output.
"""

from pathlib import Path

import torch

from openhcs.core.memory import torch as torch_function
from openhcs.core.vfs_protocol import PlateInputFile
from openhcs.processing.backends.enhance.n2v2_processor_torch import (
    N2V2UNet,
    process_large_slice,
)


@torch_function
def n2v2_denoise(
    image,
    model_file: PlateInputFile = Path("models/n2v2.pt"),
    tile_size: int = 256,
) -> torch.Tensor:
    """Denoise every plane of the stack with a trained N2V2 model.

    Args:
        image: Noisy image stack (planes, Y, X).
        model_file: Model written by ``n2v2_fit``, relative to the plate.
        tile_size: Side of the overlapping square tiles each plane is denoised in.

    Returns:
        The denoised stack as float32, in the input's intensity units.
    """
    device = image.device
    saved = torch.load(Path(model_file), map_location=device, weights_only=True)
    network = N2V2UNet(features=[64, 128, 256, 512]).to(device)
    network.load_state_dict(saved["weights"])
    network.eval()
    scale = saved["intensity_scale"]
    pixels = image.float() / scale
    denoised = torch.empty_like(pixels)
    with torch.no_grad():
        for index, plane in enumerate(pixels):
            denoised[index] = process_large_slice(plane, network, tile_size)
    return denoised * scale
