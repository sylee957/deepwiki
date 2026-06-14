import Book.ServersDrrSemantics
import Book.ServersWrrSemantics

/-! # Pseudocode syntax for the scheduler language
A concrete `[sched| … ]` notation rendering `Stmt` programs in the book's
imperative pseudocode style — `DC[i] := DC[i] + Q`, `while … do { … }`,
`send(head(i))`, `removeHead(i)` — elaborating to the `Stmt` AST of
`Book.SchedulerSemantics`. Statements are `;`-separated and grouped by
`{ … }` blocks, so the round-robin algorithms read like Algorithms 1 and
2; each is proven equal to its constructor definition by `rfl`.

The weight-counter `k` of Algorithm 2 is written `cnt` here, to avoid
globally reserving the ubiquitous identifier `k` as a keyword. The atoms
`DC`, `size`, `head`, `empty`, `send`, `removeHead`, `cnt`, `skip` are
reserved as keywords in any file importing this one (only `Book.lean`
does). -/

namespace DeepWiki

open scoped NNReal

/-- Arithmetic expressions of the scheduler pseudocode. -/
declare_syntax_cat saexp
/-- Boolean guards of the scheduler pseudocode. -/
declare_syntax_cat sbexp
/-- Statements of the scheduler pseudocode. -/
declare_syntax_cat sstmt

-- arithmetic expressions
syntax "DC" "[" term "]" : saexp
syntax "size" "(" "head" "(" term ")" ")" : saexp
syntax:65 saexp:65 " + " term:max : saexp
syntax:65 saexp:65 " - " saexp:66 : saexp
syntax num : saexp
syntax "(" saexp ")" : saexp

-- boolean guards
syntax "not" "empty" "(" term ")" : sbexp
syntax:50 saexp " ≤ " saexp : sbexp
syntax:50 "cnt" " ≤ " term:max : sbexp
syntax:35 sbexp:36 " ∧ " sbexp:35 : sbexp

-- statements
syntax "skip" : sstmt
syntax:10 sstmt:11 "; " sstmt:10 : sstmt
syntax "{" sstmt "}" : sstmt
syntax "DC" "[" term "]" " := " saexp : sstmt
syntax "cnt" " := " term:max : sstmt
syntax "cnt" "++" : sstmt
syntax "send" "(" "head" "(" term ")" ")" : sstmt
syntax "removeHead" "(" term ")" : sstmt
syntax "if " sbexp " then " sstmt:max " else " sstmt:max : sstmt
syntax "if " sbexp " then " sstmt:max : sstmt
syntax "while " sbexp " do " sstmt:max : sstmt
syntax "for " ident " do " sstmt:max : sstmt

-- elaboration brackets
syntax "[saexp| " saexp "]" : term
syntax "[sbexp| " sbexp "]" : term
syntax "[sched| " sstmt "]" : term

macro_rules
  | `([saexp| DC[$i:term]]) => `(AExp.dc $i)
  | `([saexp| size(head($i:term))]) => `(AExp.headSize $i)
  | `([saexp| $a:saexp + $c:term]) => `(AExp.add [saexp| $a] (AExp.lit $c))
  | `([saexp| $a:saexp - $b:saexp]) => `(AExp.sub [saexp| $a] [saexp| $b])
  | `([saexp| $n:num]) => `(AExp.lit $n)
  | `([saexp| ($a:saexp)]) => `([saexp| $a])

macro_rules
  | `([sbexp| not empty($i:term)]) => `(BExp.notEmpty $i)
  | `([sbexp| $a:saexp ≤ $b:saexp]) => `(BExp.le [saexp| $a] [saexp| $b])
  | `([sbexp| cnt ≤ $w:term]) => `(BExp.kLe $w)
  | `([sbexp| $b₁:sbexp ∧ $b₂:sbexp]) => `(BExp.and [sbexp| $b₁] [sbexp| $b₂])

macro_rules
  | `([sched| skip]) => `(Stmt.skip)
  | `([sched| $s:sstmt ; $t:sstmt]) => `(Stmt.seq [sched| $s] [sched| $t])
  | `([sched| { $s:sstmt }]) => `([sched| $s])
  | `([sched| DC[$i:term] := $a:saexp]) => `(Stmt.assignDc $i [saexp| $a])
  | `([sched| cnt := $c:term]) => `(Stmt.setK $c)
  | `([sched| cnt ++]) => `(Stmt.incK)
  | `([sched| send(head($i:term))]) => `(Stmt.send $i)
  | `([sched| removeHead($i:term)]) => `(Stmt.removeHead $i)
  | `([sched| if $b:sbexp then $s:sstmt else $t:sstmt]) =>
      `(Stmt.ifte [sbexp| $b] [sched| $s] [sched| $t])
  | `([sched| if $b:sbexp then $s:sstmt]) =>
      `(Stmt.ifte [sbexp| $b] [sched| $s] Stmt.skip)
  | `([sched| while $b:sbexp do $s:sstmt]) =>
      `(Stmt.whileB [sbexp| $b] [sched| $s])
  | `([sched| for $i:ident do $s:sstmt]) =>
      `(roundStmt (fun $i => [sched| $s]))

/-! ## The round-robin algorithms in pseudocode syntax
Each definition reads like the book's pseudocode and is the same `Stmt` as
the constructor form (`rfl`). -/

variable {n : ℕ}

/-- DRR inner loop (Algorithm 1, lines 7-10) in pseudocode syntax. -/
example (i : Fin n) :
    drrInner i =
      [sched|
        while not empty(i) ∧ size(head(i)) ≤ DC[i] do {
          send(head(i));
          DC[i] := DC[i] - size(head(i));
          removeHead(i)
        }] := rfl

/-- DRR per-flow turn (Algorithm 1, lines 5-12) in pseudocode syntax. -/
example (Q : ℝ≥0) (i : Fin n) :
    drrTurn Q i =
      [sched|
        if not empty(i) then {
          DC[i] := DC[i] + Q;
          while not empty(i) ∧ size(head(i)) ≤ DC[i] do {
            send(head(i));
            DC[i] := DC[i] - size(head(i));
            removeHead(i)
          };
          if not empty(i) then skip else { DC[i] := 0 }
        }] := rfl

/-- WRR per-flow turn (Algorithm 2, lines 3-7) in pseudocode syntax,
writing the weight counter `k` as `cnt`. -/
example (w : ℕ) (i : Fin n) :
    wrrTurn w i =
      [sched|
        cnt := 1;
        while not empty(i) ∧ cnt ≤ w do {
          send(head(i));
          removeHead(i);
          cnt++
        }] := rfl

/-- One DRR round (Algorithm 1, the `for i = 1 to n` over flows) in
pseudocode syntax, with per-flow quanta `Q i`. -/
example (Q : Fin n → ℝ≥0) :
    drrRound Q =
      [sched|
        for i do {
          if not empty(i) then {
            DC[i] := DC[i] + (Q i);
            while not empty(i) ∧ size(head(i)) ≤ DC[i] do {
              send(head(i));
              DC[i] := DC[i] - size(head(i));
              removeHead(i)
            };
            if not empty(i) then skip else { DC[i] := 0 }
          }
        }] := rfl

/-- One WRR round (Algorithm 2, the `for i = 1 to n` over flows) in
pseudocode syntax, with per-flow weights `w i`. -/
example (w : Fin n → ℕ) :
    wrrRound w =
      [sched|
        for i do {
          cnt := 1;
          while not empty(i) ∧ cnt ≤ (w i) do {
            send(head(i));
            removeHead(i);
            cnt++
          }
        }] := rfl

end DeepWiki
