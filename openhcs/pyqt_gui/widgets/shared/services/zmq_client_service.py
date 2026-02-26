"""
Shared ZMQ client manager for compile/run flows.
"""

from __future__ import annotations

import asyncio
import logging

logger = logging.getLogger(__name__)


class ZMQClientService:
    """Create/connect/disconnect a ZMQ execution client."""

    def __init__(self, port: int = 7777):
        self.port = port
        self.zmq_client = None

    async def connect(
        self,
        progress_callback=None,
        persistent: bool = True,
        timeout: float = 15,
    ):
        """Create a client and connect to the execution server."""
        from openhcs.runtime.zmq_execution_client import ZMQExecutionClient

        if self.zmq_client is not None and self.zmq_client.is_connected():
            existing_callback = self.zmq_client.progress_callback
            if existing_callback is progress_callback:
                return self.zmq_client
            await self.disconnect()
        loop = asyncio.get_event_loop()
        self.zmq_client = ZMQExecutionClient(
            port=self.port,
            persistent=persistent,
            progress_callback=progress_callback,
        )
        connected = await loop.run_in_executor(
            None, lambda: self.zmq_client.connect(timeout=timeout)
        )
        if not connected:
            self.zmq_client = None
            raise RuntimeError("Failed to connect to ZMQ execution server")
        logger.info("✅ Connected to ZMQ execution server")
        return self.zmq_client

    async def disconnect(self) -> None:
        """Disconnect the client (async-safe)."""
        if self.zmq_client is None:
            return
        loop = asyncio.get_event_loop()
        client = self.zmq_client
        self.zmq_client = None
        await loop.run_in_executor(None, client.disconnect)

    def disconnect_sync(self) -> None:
        """Disconnect the client (sync)."""
        if self.zmq_client is None:
            return
        try:
            self.zmq_client.disconnect()
        finally:
            self.zmq_client = None
