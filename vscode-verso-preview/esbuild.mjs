import * as esbuild from "esbuild";
import { copyFileSync, mkdirSync } from "fs";

const watch = process.argv.includes("--watch");

// Copy runtime assets the bundle can't inline: the Lean TextMate grammar and
// the oniguruma WASM regex engine. The host loads these from dist/ at runtime.
function copyAssets() {
  mkdirSync("dist", { recursive: true });
  copyFileSync("grammars/lean4.json", "dist/lean4.json");
  copyFileSync(
    "node_modules/vscode-oniguruma/release/onig.wasm",
    "dist/onig.wasm"
  );
}

/** Extension host bundle: Node/CommonJS, vscode is external. */
const hostConfig = {
  entryPoints: ["src/extension.ts"],
  bundle: true,
  outfile: "dist/extension.js",
  platform: "node",
  format: "cjs",
  target: "node18",
  external: ["vscode"],
  sourcemap: true,
  logLevel: "info",
};

/** Webview bundle: browser/IIFE, React app (+ inlined CSS). */
const webviewConfig = {
  entryPoints: ["src/webview/index.tsx"],
  bundle: true,
  outfile: "dist/webview.js",
  platform: "browser",
  format: "iife",
  target: "es2020",
  sourcemap: true,
  jsx: "automatic",
  loader: { ".css": "css" },
  define: { "process.env.NODE_ENV": '"production"' },
  logLevel: "info",
};

copyAssets();
if (watch) {
  const h = await esbuild.context(hostConfig);
  const w = await esbuild.context(webviewConfig);
  await Promise.all([h.watch(), w.watch()]);
  console.log("watching…");
} else {
  await Promise.all([esbuild.build(hostConfig), esbuild.build(webviewConfig)]);
}
