import DeepWiki.SymbolicIntegration.Engine.Algebraic.BareissExamples.Agreement

/-! # Bareiss adjugate and solve examples

Sanity checks that `bareissAdjugate` and `bareissSolve` satisfy their defining matrix identities. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

open DensePoly

/-- `M · adj M = det M · I` on the `2×2` trace matrix: the fraction-free adjugate satisfies the
defining identity over `ℚ[x]`. -/
theorem bareiss_adjugate_nonRad :
    let M := bareissNonRadT
    let A := CPoly.bareissAdjugate M
    let d := CPoly.bareissDet M
    let prod := (List.range 2).map (fun i => (List.range 2).map (fun j =>
      (List.range 2).foldl (fun acc k => cadd acc
        (cmul (CPoly.polyMatGet M i k) (CPoly.polyMatGet A k j))) []))
    (cisZero (csub (CPoly.polyMatGet prod 0 0) d)
      && cisZero (CPoly.polyMatGet prod 0 1)
      && cisZero (CPoly.polyMatGet prod 1 0)
      && cisZero (csub (CPoly.polyMatGet prod 1 1) d)) = true := by native_decide

/-- `M · adj M = det M · I` on the `3×3` trigonal trace matrix: the diagonal of `M·adj M` is
`det M = −4x³ − 27x²` and every off-diagonal entry vanishes. -/
theorem bareiss_adjugate_trig :
    let M := bareissTrigT
    let A := CPoly.bareissAdjugate M
    let d := CPoly.bareissDet M
    let prod := (List.range 3).map (fun i => (List.range 3).map (fun j =>
      (List.range 3).foldl (fun acc k => cadd acc
        (cmul (CPoly.polyMatGet M i k) (CPoly.polyMatGet A k j))) []))
    (List.range 3).all (fun i => (List.range 3).all (fun j =>
      cisZero (csub (CPoly.polyMatGet prod i j) (if i = j then d else [])))) = true := by native_decide

/-- `bareissSolve` solves `M·(det·x) = det·b` on the `2×2` trace matrix with `b = [1, x]`: multiplying
`M` by the returned solution vector recovers `det M · b`. -/
theorem bareiss_solve_nonRad :
    let M := bareissNonRadT
    let b : List (DensePoly ℚ) := [[1], [0, 1]]
    let ds := CPoly.bareissSolve M b
    let d := ds.1
    let sol := ds.2
    let lhs := (List.range 2).map (fun i =>
      (List.range 2).foldl (fun acc j => cadd acc
        (cmul (CPoly.polyMatGet M i j) (sol.getD j []))) [])
    (cisZero (csub (lhs.getD 0 []) (cmul d (b.getD 0 [])))
      && cisZero (csub (lhs.getD 1 []) (cmul d (b.getD 1 [])))) = true := by native_decide

end DeepWiki.SymbolicIntegration
