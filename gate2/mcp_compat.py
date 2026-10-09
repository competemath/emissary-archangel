"""The MCP server object and its SSE app for both generations of the `mcp` package, so a daemon started from an older environment (mcp 1.x) and one from a new
install (mcp 2.x) run the same server.py. In mcp 2.x FastMCP is called MCPServer and the transport security settings go to `sse_app` instead of the constructor
(https://py.sdk.modelcontextprotocol.io/v2/migration/)."""

from __future__ import annotations

from mcp.server.transport_security import TransportSecuritySettings

try:  # mcp 2.x
    from mcp.server.mcpserver import MCPServer as _Server

    V2 = True
except ModuleNotFoundError:  # mcp 1.x
    from mcp.server.fastmcp import FastMCP as _Server

    V2 = False

OPEN_SECURITY = TransportSecuritySettings(enable_dns_rebinding_protection=False)


def make_server(name: str):
    return _Server(name) if V2 else _Server(name, transport_security=OPEN_SECURITY)


def sse_app(server):
    return server.sse_app(transport_security=OPEN_SECURITY) if V2 else server.sse_app()
