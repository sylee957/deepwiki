import DeepWiki.ReactiveSystems.TimedRegionCode

/-! # The Alur–Dill region time-successor (executable, §4.3)
The constructive time-successor of a clock region (Alur & Dill, *A theory of timed
automata*, §4.3): the time-successors of a region form a **deterministic chain**
`γ → step γ → step² γ → …` until every clock saturates. `regionCodeStep` is one
elapse step on a region *code* (three cases: all-saturated fixpoint; a bounded integral
clock acquiring a small positive fraction; the maximal-fraction bounded clocks wrapping
to the next integer), and `regionCodeDelaySucc` is the resulting finite orbit — a fully
computable `succ : RegionCode → List RegionCode`, the enumerator the conditional full
model checker (`SymSatCodeFull`) needs. (Soundness/completeness against `regionFingerprint`
are proved separately.) -/

namespace DeepWiki.ReactiveSystems

open scoped NNReal

variable {C : Type*} [Fintype C] [DecidableEq C]

/-- A clamped floor value `Fin (cmax x + 2)` from a `ℕ` (clamped at the `cmax x + 1`
saturation sentinel). -/
def bumpFloor (cmax : C → ℕ) (x : C) (n : ℕ) : Fin (cmax x + 2) := ⟨min n (cmax x + 1), by omega⟩

/-- One Alur–Dill time-elapse step on a region code. **Case A** (every clock saturated):
fixpoint. **Case B** (some bounded integral clock): each integral clock acquires the
smallest positive fraction — clearing its frac-zero bit and becoming least in the
frac-order — or saturates if it sat at `cmax x`. **Case C** (no bounded integral clock):
the bounded clocks of maximal fraction wrap to the next integer (floor `+1`, frac `0`). -/
def regionCodeStep {cmax : C → ℕ} (γ : RegionCode cmax) : RegionCode cmax :=
  if decide (∀ x, (γ.1 x).val = cmax x + 1) = true then γ
  else if decide (∃ x, γ.2.1 x = true) = true then
    let nowSat : C → Bool := fun x =>
      decide ((γ.1 x).val = cmax x + 1) || (γ.2.1 x && decide ((γ.1 x).val = cmax x))
    let nowSmall : C → Bool := fun x => γ.2.1 x && decide ((γ.1 x).val < cmax x)
    (fun x => if nowSat x = true then bumpFloor cmax x (cmax x + 1) else γ.1 x,
     fun _ => false,
     fun x y =>
       if (nowSat x || nowSat y) = true then false
       else if nowSmall x = true then true
       else if nowSmall y = true then false
       else γ.2.2 x y)
  else
    let isMax : C → Bool := fun x =>
      decide ((γ.1 x).val ≤ cmax x) && decide (∀ y, (γ.1 y).val ≤ cmax y → γ.2.2 y x = true)
    (fun x => if isMax x = true then bumpFloor cmax x ((γ.1 x).val + 1) else γ.1 x,
     fun x => isMax x,
     fun x y =>
       if (decide ((γ.1 x).val = cmax x + 1) || decide ((γ.1 y).val = cmax y + 1)) = true then false
       else if isMax x = true then true
       else if isMax y = true then false
       else γ.2.2 x y)

/-- The orbit of `regionCodeStep` from `γ`, collected until a fixpoint (bounded by `fuel`). -/
def regionCodeOrbit {cmax : C → ℕ} : ℕ → RegionCode cmax → List (RegionCode cmax)
  | 0, γ => [γ]
  | fuel + 1, γ =>
      let γ' := regionCodeStep γ
      if γ' = γ then [γ] else γ :: regionCodeOrbit fuel γ'

/-- The **time-successors of a region code**: the finite orbit of the elapse step. The fuel
`2·∑ₓ(cₓ+1) + |C|` dominates the descent measure of every code, so the chain always saturates
within it. The computable `succ` enumerator for the full model checker. -/
def regionCodeDelaySucc {cmax : C → ℕ} (γ : RegionCode cmax) : List (RegionCode cmax) :=
  regionCodeOrbit (2 * (∑ x, (cmax x + 1)) + Fintype.card C) γ

/-! ## Worked example (Alur–Dill Example 4.7, single clamp) -/

/-- Two clocks `x, y`, both clamped at `1`. -/
def cmaxEx : Fin 2 → ℕ := fun _ => 1

/-- The region `0 < y < x < 1` (both fractional, `x` the larger): floors `0`, neither
integral, frac-order `frac y ≤ frac x` only. -/
def startCode : RegionCode cmaxEx :=
  (fun _ => ⟨0, by omega⟩, fun _ => false,
   fun i j => decide (i = j) || (decide (i = 1) && decide (j = 0)))

-- The elapse chain from `0 < y < x < 1` runs `x→1`, `x>1`, `y→1`, `y>1`, then saturates:
-- five regions in the orbit.
set_option maxRecDepth 4000 in
example : (regionCodeOrbit 10 startCode).length = 5 := by decide

end DeepWiki.ReactiveSystems
