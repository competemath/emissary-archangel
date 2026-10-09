import type { NextConfig } from "next";

const nextConfig: NextConfig = {
  // The console shows no raster images, so Next's image optimizer (the only user of sharp and its LGPL libvips binaries) is switched off
  // and sharp is not installed (the "overrides" entry in package.json).
  images: { unoptimized: true },
  env: {
    // Baked into the console's bridge setup command so a downloaded bridge
    // finds this checkout (corpus checkouts, exports, prefix cache).
    NEXT_PUBLIC_EMISSARY_APP_ROOT: process.cwd(),
  },
};

export default nextConfig;
