// Minimal build script using esbuild to create a standalone viewer.bundle.js
const { build } = require('esbuild');
const fs = require('fs');
const path = require('path');

const args = process.argv.slice(2);
const serve = args.includes('--serve');

async function doBuild() {
  const outdir = path.resolve(__dirname);
  try {
    await build({
      entryPoints: [path.resolve(__dirname, 'dependency-graph.jsx')],
      bundle: true,
      minify: false,
      sourcemap: false,
      outfile: path.join(outdir, 'viewer.bundle.js'),
      loader: { '.jsx': 'jsx' },
      define: { 'process.env.NODE_ENV': '"production"' }
    });
    console.log('Built viewer.bundle.js');
  } catch (e) {
    console.error('Build failed', e);
    process.exit(1);
  }
}

if (serve) {
  // Simple static file server for quick testing
  const express = require('express');
  const app = express();
  app.use(express.static(path.resolve(__dirname)));
  const port = 5173;
  app.listen(port, () => {
    console.log(`Serving ${__dirname} at http://localhost:${port}`);
  });
  doBuild();
} else {
  doBuild();
}
