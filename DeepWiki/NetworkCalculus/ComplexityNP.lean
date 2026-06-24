import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Computability.Encoding
import DeepWiki.NetworkCalculus.KarpReduction

/-! # A Turing-machine-grounded NP class
This file builds the **genuine** complexity class NP on top of Mathlib's finite-Turing-machine
poly-time model `Turing.TM2ComputableInPolyTime`, and relates it to the lightweight certificate-size
proxy `IsInNP` (`KarpReduction.lean`) used by DNC Theorem 10.2.

The proxy `IsInNP` deliberately discards the computation model — its verifier is a *merely decidable*
predicate with a polynomially-bounded certificate, NOT a poly-*time* machine. That proxy cannot host the
Cook–Levin theorem (a decidable check need not be encodable as a polynomially-sized Boolean formula).
The class here keeps the missing structure: the verifier is a **real polynomial-time finite TM2**
(`verify_polyTime`). This is what an eventual Cook–Levin proof must consume.

* `IsInNP_TM` — `L ∈ NP`: a poly-time TM2 verifier + a polynomially-bounded certificate.
* `IsInNP_TM.toIsInNP` — the bridge: TM-NP membership implies the proxy (forgetting the time bound),
  so every result stated over the proxy specializes the genuine class.
* `IsNPHard_TM` / `IsNPComplete_TM` — NP-hardness/completeness over the genuine class; the proxy
  `IsNPHard` is *stronger* (quantifies over more problems), so `IsNPHard.toIsNPHard_TM` transfers it.
-/

namespace DeepWiki

open Turing Computability Polynomial

/-- A decision problem `L : α → Prop` is in **NP** (Turing-machine-grounded), relative to an
instance encoding `ea : α → List αΓ`. It bundles a certificate type `Cert`, a verifier-input encoding
`einput : α × Cert → List Γ`, a Boolean verifier `verify` that is **polynomial-time computable by a
finite TM2** (`verify_polyTime`), a certificate-size measure `certSize`, and a polynomial `certPoly`,
with: every *accepted* certificate is polynomially bounded (`cert_bound`), and `L x` holds iff some
certificate is accepted (`spec`). The poly-*time* verifier is exactly the structure the proxy
`IsInNP` lacks. -/
structure IsInNP_TM {α αΓ : Type} (ea : α → List αΓ) (L : α → Prop) where
  /-- the certificate type -/
  Cert : Type
  /-- the verifier's tape alphabet -/
  Γ : Type
  /-- encoding of the instance `x` (the **fixed** prefix of the verifier input) -/
  einstance : α → List Γ
  /-- encoding of the certificate (the **free** suffix of the verifier input, appended after the
  instance) — separability is what lets a SAT reduction fix `x` and quantify over `cert`. -/
  ecert : Cert → List Γ
  /-- the size of a certificate -/
  certSize : Cert → ℕ
  /-- the Boolean verifier -/
  verify : α × Cert → Bool
  /-- the verifier runs in polynomial time on a finite TM2, reading the instance-then-certificate
  input `einstance x ++ ecert c` — the genuine poly-time witness. -/
  verify_polyTime :
    TM2ComputableInPolyTime (fun p : α × Cert => einstance p.1 ++ ecert p.2) encodeBool verify
  /-- the polynomial bounding certificate size in input size -/
  certPoly : Polynomial ℕ
  /-- every accepted certificate is polynomially bounded in the input size -/
  cert_bound : ∀ x c, verify (x, c) = true → certSize c ≤ certPoly.eval (ea x).length
  /-- soundness and completeness: `L x` holds iff some certificate is accepted -/
  spec : ∀ x, L x ↔ ∃ c : Cert, verify (x, c) = true

/-- The assembled verifier input on instance `x` with certificate `c`: the instance encoding followed
by the certificate encoding (`einstance x ++ ecert c`). -/
def IsInNP_TM.einput {α αΓ : Type} {ea : α → List αΓ} {L : α → Prop} (h : IsInNP_TM ea L) :
    α × h.Cert → List h.Γ := fun p => h.einstance p.1 ++ h.ecert p.2

/-- **Bridge: TM-grounded NP membership implies the certificate-size proxy `IsInNP`** (forgetting the
poly-*time* verifier, keeping decidability + the certificate-size bound). So any theorem proved against
the proxy (e.g. the DNC Theorem 10.2 machinery) applies to the genuine class. -/
noncomputable def IsInNP_TM.toIsInNP {α αΓ : Type} {ea : α → List αΓ} {L : α → Prop}
    (h : IsInNP_TM ea L) : IsInNP (fun x => (ea x).length) L where
  Cert := h.Cert
  sizeCert := h.certSize
  check x c := h.verify (x, c) = true
  decCheck _ _ := inferInstance
  certPoly := h.certPoly
  spec x := by
    refine ⟨fun hx => ?_, fun ⟨c, _, hc⟩ => (h.spec x).2 ⟨c, hc⟩⟩
    obtain ⟨c, hc⟩ := (h.spec x).1 hx
    exact ⟨c, h.cert_bound x c hc, hc⟩

/-- **`Q` is NP-hard** (Turing-machine-grounded): every TM-grounded NP problem Karp-reduces to `Q`
(sizes taken as encoding lengths). This is the genuine NP-hardness notion — the one an eventual
Cook–Levin proof discharges for SAT. The NP *membership* side (`α`) stays `Type` (it must be encodable
to a TM tape), but the **target** `τ` is `Type*` — so `Q` may be a bundled `Type 1` decision problem
(e.g. `WellFormedX3C`, `worstCaseBacklogDecision`), which is exactly what the DNC chain needs. -/
def IsNPHard_TM {τ : Type*} {τΓ : Type*} (eb : τ → List τΓ) (Q : τ → Prop) : Prop :=
  ∀ (α αΓ : Type) (ea : α → List αΓ) (L : α → Prop),
    IsInNP_TM ea L →
      Nonempty (KarpReduction (fun x => (ea x).length) (fun y => (eb y).length) L Q)

/-- **`Q` is NP-complete** (Turing-machine-grounded): in NP and NP-hard. -/
structure IsNPComplete_TM {τ τΓ : Type} (eb : τ → List τΓ) (Q : τ → Prop) : Prop where
  /-- `Q` is itself in NP. -/
  mem : Nonempty (IsInNP_TM eb Q)
  /-- `Q` is NP-hard. -/
  hard : IsNPHard_TM eb Q

/-- The proxy `IsNPHard` is **stronger** than TM-grounded NP-hardness: it asks `Q` to be hard for the
*larger* class of certificate-proxy-NP problems, which (via `IsInNP_TM.toIsInNP`) includes every
TM-grounded NP problem. So proxy NP-hardness transfers to the genuine notion. -/
theorem IsNPHard.toIsNPHard_TM {τ : Type*} {τΓ : Type*} {eb : τ → List τΓ} {Q : τ → Prop}
    (h : IsNPHard (fun y => (eb y).length) Q) : IsNPHard_TM eb Q :=
  fun _ _ ea L hL => h _ (fun x => (ea x).length) L hL.toIsInNP

/-- **NP-hardness propagates along Karp reductions**: if `Q` is NP-hard and `Q ≤ₖ R`, then `R` is
NP-hard (compose every NP-problem-to-`Q` reduction with `Q → R`). This is the chain mechanism — given
an NP-hard seed (Cook–Levin's SAT), a path of reductions to a target proves the target NP-hard. -/
theorem IsNPHard_TM.viaReduction {τ : Type*} {τΓ : Type*} {ρ : Type*} {ρΓ : Type*}
    {eb : τ → List τΓ} {ec : ρ → List ρΓ}
    {Q : τ → Prop} {R : ρ → Prop} (hQ : IsNPHard_TM eb Q)
    (red : KarpReduction (fun y => (eb y).length) (fun z => (ec z).length) Q R) :
    IsNPHard_TM ec R :=
  fun _ _ ea L hL => (hQ _ _ ea L hL).elim fun r => ⟨red.comp r⟩

end DeepWiki
