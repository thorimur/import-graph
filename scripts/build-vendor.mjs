// Bundle Sigma + graphology + extensions into a single self-contained IIFE
// that exposes globals expected by `html-template/index.html`. Run via
// `npm run build-vendor` (or `node scripts/build-vendor.mjs`) after bumping
// the npm dependencies in `package.json`, and commit the regenerated output.

import { build } from "esbuild";
import { fileURLToPath } from "node:url";
import { dirname, join } from "node:path";

const repoRoot = dirname(dirname(fileURLToPath(import.meta.url)));

await build({
  entryPoints: [join(repoRoot, "scripts/vendor-entry.mjs")],
  outfile: join(repoRoot, "html-template/vendor/sigma-bundle.min.js"),
  bundle: true,
  minify: true,
  format: "iife",
  target: "es2020",
  legalComments: "none",
});

console.log("Wrote html-template/vendor/sigma-bundle.min.js");
