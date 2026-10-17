"""Noise2Void (N2V2) training as an OpenHCS custom function: images in, model file out.

Register this source, then ``n2v2_denoise`` from the neighbouring file. The
network and the blind-spot helpers are the ones OpenHCS ships in
``openhcs.processing.backends.enhance.n2v2_processor_torch``; this file only
splits "fit" from "denoise" so the model is a declared file.
"""

from pathlib import Path

import torch

from openhcs.core.memory import torch as torch_function
from openhcs.core.vfs_protocol import PlateOutputFile
from openhcs.processing.backends.enhance.n2v2_processor_torch import (
    N2V2UNet,
    extract_patches_vectorized,
    generate_masks_vectorized,
    vectorized_median_replacement,
)


@torch_function
def n2v2_fit(
    image,
    model_file: PlateOutputFile = Path("models/n2v2.pt"),
    epochs: int = 10,
    patches_per_epoch: int = 128,
    patch_size: int = 64,
    batch_size: int = 8,
    blindspot_fraction: float = 0.05,
    learning_rate: float = 1e-4,
    seed: int = 42,
) -> torch.Tensor:
    """Train an N2V2 denoiser on the image stack and write it to ``model_file``.

    The stack this step receives is the whole training set: one model is
    written per call. The image is passed on unchanged.

    Args:
        image: Noisy image stack (planes, Y, X).
        model_file: Where to write the trained model, relative to the plate.
        epochs: Passes over ``patches_per_epoch`` random patches.
        patches_per_epoch: Random patches drawn from the stack in each epoch.
        patch_size: Side of the square training patches in pixels.
        batch_size: Patches per optimiser step.
        blindspot_fraction: Fraction of patch pixels masked for the blind-spot loss.
        learning_rate: AdamW learning rate.
        seed: Seed for patch sampling, masking and weight initialisation.

    Returns:
        The unchanged image.
    """
    device = image.device
    generator_state = torch.random.get_rng_state()
    torch.manual_seed(seed)
    pixels = image.float()
    scale = float(pixels.max().clamp(min=1.0))
    pixels = pixels / scale

    network = N2V2UNet(features=[64, 128, 256, 512]).to(device)
    optimiser = torch.optim.AdamW(network.parameters(), lr=learning_rate, weight_decay=0.01)
    schedule = torch.optim.lr_scheduler.CosineAnnealingLR(optimiser, epochs)
    network.train()
    final_loss = float("nan")
    for _ in range(epochs):
        for start in range(0, patches_per_epoch, batch_size):
            count = min(batch_size, patches_per_epoch - start)
            patches = extract_patches_vectorized(pixels, patch_size, count)
            masks = generate_masks_vectorized(
                count, patch_size, patch_size, blindspot_fraction, device
            )
            prediction = network(vectorized_median_replacement(patches, masks).unsqueeze(1))
            error = (prediction.squeeze(1) - patches) ** 2
            loss = (error * masks).sum() / masks.sum().clamp(min=1)
            optimiser.zero_grad()
            loss.backward()
            torch.nn.utils.clip_grad_norm_(network.parameters(), 1.0)
            optimiser.step()
            final_loss = float(loss.detach())
        schedule.step()
    torch.random.set_rng_state(generator_state)

    model_file = Path(model_file)
    model_file.parent.mkdir(parents=True, exist_ok=True)
    torch.save(
        {
            "weights": {name: value.cpu() for name, value in network.state_dict().items()},
            "intensity_scale": scale,
            "training": {
                "epochs": epochs,
                "patches_per_epoch": patches_per_epoch,
                "patch_size": patch_size,
                "batch_size": batch_size,
                "blindspot_fraction": blindspot_fraction,
                "learning_rate": learning_rate,
                "seed": seed,
                "planes": int(image.shape[0]),
                "final_loss": final_loss,
            },
        },
        model_file,
    )
    return image
