import type { NextConfig } from "next";

const nextConfig: NextConfig = {
  env: {
    // Baked into the console's bridge setup command so a downloaded bridge
    // finds this checkout (corpus checkouts, exports, prefix cache).
    NEXT_PUBLIC_EMISSARY_APP_ROOT: process.cwd(),
  },
};

export default nextConfig;
