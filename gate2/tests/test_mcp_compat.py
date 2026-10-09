"""server.py runs on both generations of the `mcp` package through gate2/mcp_compat.py: FastMCP in 1.x, MCPServer in 2.x with the transport security settings given to
`sse_app`. Skipped where `mcp` is not installed (the Lean workflow does not install it); run it in each environment the daemon may start from."""

from __future__ import annotations

import importlib.util
import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
HAVE_MCP = importlib.util.find_spec("mcp") is not None


@unittest.skipUnless(HAVE_MCP, "mcp is not installed")
class McpCompat(unittest.TestCase):
    def test_the_server_registers_a_tool_and_serves_an_sse_app_that_accepts_any_host(self):
        import mcp_compat as mc

        server = mc.make_server("Emissary-Archangel-Gate2")

        @server.tool()
        async def ping(x: str) -> str:
            return "pong " + x

        app = mc.sse_app(server)
        self.assertTrue(callable(app))
        paths = {getattr(r, "path", None) for r in app.routes}
        self.assertIn("/sse", paths)
        self.assertIn("/messages", {p.rstrip("/") for p in paths if p})

    def test_the_security_settings_are_the_open_ones_in_both_generations(self):
        import mcp_compat as mc

        self.assertFalse(mc.OPEN_SECURITY.enable_dns_rebinding_protection)
        self.assertIsInstance(mc.V2, bool)


if __name__ == "__main__":
    unittest.main()
