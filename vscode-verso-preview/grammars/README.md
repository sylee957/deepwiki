# Vendored grammar

`lean4.json` is the Lean 4 TextMate grammar, copied verbatim from the official
Lean 4 VS Code extension (`leanprover.lean4`, `syntaxes/lean4.json`). It is used
by the preview to color Lean code blocks (the base layer; LSP semantic tokens
refine it). Licensed Apache-2.0, same as Lean 4.

To refresh it after a Lean extension update:

    cp ~/.vscode/extensions/leanprover.lean4-*/syntaxes/lean4.json \
       vscode-verso-preview/grammars/lean4.json
