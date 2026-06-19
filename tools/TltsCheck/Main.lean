import TltsCheck.Basic

/-! # `tlts` — CLI for the formally-verified timed model checker
Increment 1: runs the verified `check` on a built-in demo (proves the exe pipeline links the
native checker). JSON-spec input and the SQLite-backed library follow. -/

open TltsCheck DeepWiki.ReactiveSystems

/-- A built-in demo: `demoAuto` = one self-loop `a` guarded `x ≤ 1`, resetting `x`, invariant
`x ≤ 2`. We check two timed-HML properties against it. -/
def demos : List (String × Bool) :=
  [ ("demoAuto ⊨ ∃∃ [a] ff   (a delay reaches a state with no a-move)",
      check demoAuto (Mt.existsDelay (Mt.box () Mt.ff) : Mt Unit (Fin 1))),
    ("demoAuto ⊨ ∀∀ ⟨a⟩ tt   (every delay keeps an a-move enabled)",
      check demoAuto (Mt.forallDelay (Mt.dia () Mt.tt) : Mt Unit (Fin 1))) ]

def main (_args : List String) : IO Unit := do
  IO.println "tlts — formally-verified timed model checker (DeepWiki ReactiveSystems)"
  IO.println "checker = SymSatCodeFull ∘ regionCodeDelaySucc, proved = ⊨ by check_iff\n"
  for (name, result) in demos do
    IO.println s!"  {if result then "true " else "false"}   {name}"
