// esbuild bundles `import "./styles.css"` as a side effect; TypeScript needs a
// declaration so the side-effect import type-checks.
declare module "*.css";
