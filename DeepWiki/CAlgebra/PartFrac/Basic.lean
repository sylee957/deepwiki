import DeepWiki.CAlgebra.Squarefree.Dense
import Mathlib.FieldTheory.RatFunc.Basic

/-! # Squarefree partial fraction decomposition

`a/p = poly + Σᵢ Σⱼ aᵢⱼ/dᵢʲ` over the squarefree decomposition `p ~ ∏ dᵢⁱ`: the Bézout
two-term split `splitCoprime`, the `f`-adic numerator expansion `adicExpand`, and the sweep
`partFracAux` assembling them along the staircase, dispatched through `DensePolySquarefree`.
Specs are polynomial identities plus the semantic reading in `RatFunc R` through
`toRatFuncHom`; every numerator is reduced modulo its factor. -/

namespace DeepWiki.CAlgebra

universe u

namespace DensePoly

variable {R : Type u} [Field R] [DecidableEq R]

/-! ### The Bézout two-term split -/

/-- First scaled Bézout coefficient: `bezA u v * u + bezB u v * v = 1` for coprime inputs. -/
def bezA (u v : DensePoly R) : DensePoly R :=
  EuclideanDomain.gcdA u v * C ((EuclideanDomain.gcd u v).coeff 0)⁻¹

/-- Second scaled Bézout coefficient (see `bezA`). -/
def bezB (u v : DensePoly R) : DensePoly R :=
  EuclideanDomain.gcdB u v * C ((EuclideanDomain.gcd u v).coeff 0)⁻¹

/-- The scaled Bézout identity: for coprime `u, v` the extended Euclidean coefficients scaled
by the inverse of the constant gcd witness `1 = bezA·u + bezB·v`. -/
theorem bezA_mul_add_bezB_mul {u v : DensePoly R} (h : IsCoprime u v) :
    bezA u v * u + bezB u v * v = 1 := by
  have hg : IsUnit (EuclideanDomain.gcd u v) :=
    h.isUnit_of_dvd' (EuclideanDomain.gcd_dvd_left u v) (EuclideanDomain.gcd_dvd_right u v)
  have hs : (EuclideanDomain.gcd u v).size = 1 := isUnit_iff_size_eq_one.mp hg
  have hγ : (EuclideanDomain.gcd u v).coeff 0 ≠ 0 := by
    have h1 := coeff_last_ne_zero_of_pos_size (EuclideanDomain.gcd u v) (by omega)
    rwa [hs] at h1
  have hkey : (u * EuclideanDomain.gcdA u v + v * EuclideanDomain.gcdB u v)
      * C ((EuclideanDomain.gcd u v).coeff 0)⁻¹ = 1 := by
    rw [← EuclideanDomain.gcd_eq_gcd_ab]
    nth_rewrite 1 [eq_C_of_size_eq_one hs]
    rw [← C_mul, mul_inv_cancel₀ hγ, ← one_def]
  calc bezA u v * u + bezB u v * v
      = (u * EuclideanDomain.gcdA u v + v * EuclideanDomain.gcdB u v)
        * C ((EuclideanDomain.gcd u v).coeff 0)⁻¹ := by rw [bezA, bezB]; ring
    _ = 1 := hkey

/-- Split `a/(u·v)` into `b/u + c/v` for coprime `u, v`: `b` is reduced modulo `u`. -/
def splitCoprime (a u v : DensePoly R) : DensePoly R × DensePoly R :=
  (mod (a * bezB u v) u, a * bezA u v + v * div (a * bezB u v) u)

/-- The split reconstructs the numerator: `b·v + c·u = a`. -/
theorem splitCoprime_spec {u v : DensePoly R} (h : IsCoprime u v) (a : DensePoly R) :
    (splitCoprime a u v).1 * v + (splitCoprime a u v).2 * u = a := by
  rw [splitCoprime, mod_eq_sub]
  calc (a * bezB u v - div (a * bezB u v) u * u) * v
        + (a * bezA u v + v * div (a * bezB u v) u) * u
      = a * (bezA u v * u + bezB u v * v) := by ring
    _ = a := by rw [bezA_mul_add_bezB_mul h, mul_one]

/-- The `u`-numerator of the split is reduced: its size is below `u`'s. -/
theorem splitCoprime_size_lt {u : DensePoly R} (hu : u.size ≠ 0) (a v : DensePoly R) :
    (splitCoprime a u v).1.size < u.size := mod_size_lt hu _

/-! ### The `f`-adic expansion -/

/-- `f`-adic expansion `adicExpand n a f = (poly, [a₁, …, aₙ])`:
`a = poly·fⁿ + Σⱼ aⱼ·fⁿ⁻ʲ` with each `aⱼ` reduced modulo `f` (Horner recombination in
`adicExpand_foldl`). -/
def adicExpand : ℕ → DensePoly R → DensePoly R → DensePoly R × List (DensePoly R)
  | 0, a, _ => (a, [])
  | n + 1, a, f =>
      ((adicExpand n (div a f) f).1, (adicExpand n (div a f) f).2 ++ [mod a f])

/-- Horner recombination: the expansion reconstructs `a`. -/
theorem adicExpand_foldl (n : ℕ) (a f : DensePoly R) :
    (adicExpand n a f).2.foldl (fun acc x => acc * f + x) (adicExpand n a f).1 = a := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih =>
      rw [adicExpand, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      rw [ih]
      exact divMod_spec a f

/-- Every numerator of the expansion is reduced modulo `f`. -/
theorem adicExpand_size_lt {f : DensePoly R} (hf : f.size ≠ 0) (n : ℕ) (a : DensePoly R) :
    ∀ b ∈ (adicExpand n a f).2, b.size < f.size := by
  induction n generalizing a with
  | zero => intro b hb; exact absurd hb (List.not_mem_nil)
  | succ n ih =>
      intro b hb
      rw [adicExpand] at hb
      rcases List.mem_append.mp hb with h | h
      · exact ih (div a f) b h
      · rw [List.mem_singleton] at h
        subst h
        exact mod_size_lt hf a

/-- The expansion emits exactly `n` numerators. -/
theorem adicExpand_length (n : ℕ) (a f : DensePoly R) :
    (adicExpand n a f).2.length = n := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih => simp [adicExpand, ih]

/-! ### The rational-function reading -/

/-- The dense polynomial ring inside `RatFunc R` (spec-level ring hom through the bridge). -/
noncomputable def toRatFuncHom : DensePoly R →+* RatFunc R :=
  (algebraMap (Polynomial R) (RatFunc R)).comp (equiv (R := R)).toRingHom

/-- `toRatFuncHom` reads as the algebra map applied to the bridged polynomial. -/
theorem toRatFuncHom_apply (p : DensePoly R) :
    toRatFuncHom p = algebraMap (Polynomial R) (RatFunc R) (toPolynomial p) := rfl

/-- `toRatFuncHom` sends nonzero polynomials to nonzero rational functions. -/
theorem toRatFuncHom_ne_zero {p : DensePoly R} (hp : p ≠ 0) :
    (toRatFuncHom p : RatFunc R) ≠ 0 := by
  rw [toRatFuncHom_apply]
  exact RatFunc.algebraMap_ne_zero (toPolynomial_ne_zero hp)

/-- `invPowSum F [x₁, …, xₙ] = Σⱼ xⱼ / Fʲ`, as a Horner fold in `1/F`. -/
noncomputable def invPowSum (F : RatFunc R) (xs : List (RatFunc R)) : RatFunc R :=
  xs.foldr (fun x acc => (x + acc) / F) 0

omit [DecidableEq R] in
/-- Seeding the `invPowSum` fold adds the seed at depth `xs.length`. -/
theorem foldr_div_seed (F : RatFunc R) (xs : List (RatFunc R)) (i : RatFunc R) :
    xs.foldr (fun x acc => (x + acc) / F) i
      = invPowSum F xs + i / F ^ xs.length := by
  induction xs with
  | nil => simp [invPowSum]
  | cons x T ih =>
      simp only [List.foldr_cons, invPowSum, List.length_cons] at *
      rw [ih, ← add_assoc, add_div, div_div, ← pow_succ]

omit [DecidableEq R] in
/-- Reversed-cons decomposition: prepending to a descending list adds its term at the top
exponent. -/
theorem invPowSum_reverse_cons (F : RatFunc R) (x : RatFunc R) (L : List (RatFunc R)) :
    invPowSum F (L.reverse ++ [x])
      = invPowSum F L.reverse + x / F ^ (L.length + 1) := by
  rw [invPowSum, List.foldr_append]
  show List.foldr _ ((x + 0) / F) _ = _
  rw [foldr_div_seed, add_zero, List.length_reverse, div_div, ← pow_succ']

/-- The `f`-adic expansion under `toRatFuncHom`: `a/fⁿ = poly + Σⱼ aⱼ/fʲ`. -/
theorem adicExpand_ratFunc {f : DensePoly R} (hf : f ≠ 0) (n : ℕ) (a : DensePoly R) :
    toRatFuncHom a / toRatFuncHom f ^ n
      = toRatFuncHom (adicExpand n a f).1
        + invPowSum (toRatFuncHom f) ((adicExpand n a f).2.map toRatFuncHom) := by
  induction n generalizing a with
  | zero => simp [adicExpand, invPowSum]
  | succ n ih =>
      rw [adicExpand]
      simp only [List.map_append, List.map_cons, List.map_nil]
      have hlen : ((adicExpand n (div a f) f).2.map toRatFuncHom).length = n := by
        rw [List.length_map, adicExpand_length]
      have hsplit : invPowSum (toRatFuncHom f)
            (((adicExpand n (div a f) f).2.map toRatFuncHom) ++ [toRatFuncHom (mod a f)])
          = invPowSum (toRatFuncHom f) ((adicExpand n (div a f) f).2.map toRatFuncHom)
            + toRatFuncHom (mod a f) / toRatFuncHom f ^ (n + 1) := by
        rw [invPowSum, List.foldr_append]
        show List.foldr _ ((toRatFuncHom (mod a f) + 0) / toRatFuncHom f) _ = _
        rw [foldr_div_seed, add_zero, hlen, div_div, ← pow_succ']
      rw [hsplit]
      have hdm : div a f * f + mod a f = a := divMod_spec a f
      calc toRatFuncHom a / toRatFuncHom f ^ (n + 1)
          = (toRatFuncHom (div a f) * toRatFuncHom f + toRatFuncHom (mod a f))
              / toRatFuncHom f ^ (n + 1) := by rw [← map_mul, ← map_add, hdm]
        _ = toRatFuncHom (div a f) / toRatFuncHom f ^ n
              + toRatFuncHom (mod a f) / toRatFuncHom f ^ (n + 1) := by
            rw [add_div, pow_succ,
              mul_div_mul_right _ _ (toRatFuncHom_ne_zero hf)]
        _ = _ := by rw [ih, add_assoc]

/-! ### The partial fraction sweep -/

/-- Partial fraction sweep over the staircase `powProd L n`: split off `f₁ⁿ` by Bézout,
expand its numerator `f₁`-adically, recurse on the tail with exponent `n+1`. Returns the
polynomial part and per-factor numerator lists (ascending exponent). -/
def partFracAux : DensePoly R → List (DensePoly R) → ℕ →
    DensePoly R × List (DensePoly R × List (DensePoly R))
  | a, [], _ => (a, [])
  | a, f :: T, n =>
    let bc := splitCoprime a (f ^ n) (powProd T (n + 1))
    let pe := adicExpand n bc.1 f
    let rest := partFracAux bc.2 T (n + 1)
    (pe.1 + rest.1, (f, pe.2) :: rest.2)

/-- The semantic value of a per-factor numerator table: `Σᵢ Σⱼ aᵢⱼ/dᵢʲ`. -/
noncomputable def partsSum (parts : List (DensePoly R × List (DensePoly R))) : RatFunc R :=
  (parts.map fun fa => invPowSum (toRatFuncHom fa.1) (fa.2.map toRatFuncHom)).sum

/-- The sweep's factor column is exactly the input factor list. -/
theorem partFracAux_fst :
    ∀ (L : List (DensePoly R)) (a : DensePoly R) (n : ℕ),
      ((partFracAux a L n).2.map Prod.fst) = L := by
  intro L
  induction L with
  | nil => intro a n; rfl
  | cons f T ih =>
      intro a n
      simp only [partFracAux, List.map_cons]
      rw [ih]

/-- Every numerator emitted by the sweep is reduced modulo its factor. -/
theorem partFracAux_size_lt :
    ∀ (L : List (DensePoly R)) (a : DensePoly R) (n : ℕ), (∀ f ∈ L, f ≠ 0) →
      ∀ fa ∈ (partFracAux a L n).2, ∀ b ∈ fa.2, b.size < fa.1.size := by
  intro L
  induction L with
  | nil => intro a n _ fa hfa; exact absurd hfa (List.not_mem_nil)
  | cons f T ih =>
      intro a n hne fa hfa
      simp only [partFracAux] at hfa
      rcases List.mem_cons.mp hfa with rfl | hfa
      · intro b hb
        exact adicExpand_size_lt
          (fun h0 => hne f (by simp) (eq_zero_of_size_zero h0)) n _ b hb
      · exact ih _ (n + 1) (fun x hx => hne x (by simp [hx])) fa hfa

variable [DensePolyGcd R]

/-- **The sweep is a partial fraction decomposition**: over `RatFunc R`,
`a / ∏ᵢ fᵢ^(n+i) = poly + Σᵢ Σⱼ aᵢⱼ/fᵢʲ`, given nonzero factors with squarefree product. -/
theorem partFracAux_ratFunc :
    ∀ (L : List (DensePoly R)) (a : DensePoly R) (n : ℕ),
      (∀ f ∈ L, f ≠ 0) → Squarefree L.prod →
      toRatFuncHom a / toRatFuncHom (powProd L n)
        = toRatFuncHom (partFracAux a L n).1 + partsSum (partFracAux a L n).2 := by
  intro L
  induction L with
  | nil =>
      intro a n _ _
      simp [partFracAux, partsSum, powProd]
  | cons f T ih =>
      intro a n hne hsf
      have hf0 : f ≠ 0 := hne f (by simp)
      have hT0 : ∀ x ∈ T, x ≠ 0 := fun x hx => hne x (by simp [hx])
      have hTsf : Squarefree T.prod := by
        rw [List.prod_cons] at hsf
        exact hsf.squarefree_of_dvd (Dvd.intro_left f rfl)
      have hcop : IsCoprime (f ^ n) (powProd T (n + 1)) := by
        refine IsCoprime.pow_left ?_
        rw [List.prod_cons] at hsf
        exact isCoprime_powProd_of_squarefree hf0 hsf (n + 1)
      have hsplit := splitCoprime_spec hcop a
      have hv0 : powProd T (n + 1) ≠ 0 := powProd_ne_zero hT0 _
      have hu0 : (f ^ n : DensePoly R) ≠ 0 := pow_ne_zero _ hf0
      simp only [partFracAux]
      set bc := splitCoprime a (f ^ n) (powProd T (n + 1)) with hbc
      have key : toRatFuncHom a
            / (toRatFuncHom (f ^ n) * toRatFuncHom (powProd T (n + 1)))
          = toRatFuncHom bc.1 / toRatFuncHom (f ^ n)
            + toRatFuncHom bc.2 / toRatFuncHom (powProd T (n + 1)) := by
        have h1 : toRatFuncHom a
            = toRatFuncHom bc.1 * toRatFuncHom (powProd T (n + 1))
              + toRatFuncHom bc.2 * toRatFuncHom (f ^ n) := by
          rw [← map_mul, ← map_mul, ← map_add, hsplit]
        rw [h1, add_div]
        congr 1
        · exact mul_div_mul_right _ _ (toRatFuncHom_ne_zero hv0)
        · rw [mul_comm (toRatFuncHom (f ^ n)) (toRatFuncHom (powProd T (n + 1)))]
          exact mul_div_mul_right _ _ (toRatFuncHom_ne_zero hu0)
      rw [show powProd (f :: T) n = f ^ n * powProd T (n + 1) from rfl, map_mul, key,
        map_pow, adicExpand_ratFunc hf0 n bc.1, ih bc.2 (n + 1) hT0 hTsf, map_add]
      simp only [partsSum, List.map_cons, List.sum_cons]
      ring

variable [DensePolySquarefree R] [CharZero R]

/-- **Squarefree partial fraction decomposition** of `a/p`: decompose `p` through the
dispatched squarefree decomposition, absorb the reconstruction constant into the numerator,
and run the sweep. Returns the polynomial part and, per squarefree factor `dᵢ` (of exponent
`i`), the numerators `[aᵢ₁, …, aᵢᵢ]`. -/
def sqfPartFrac (a p : DensePoly R) :
    DensePoly R × List (DensePoly R × List (DensePoly R)) :=
  partFracAux (a * div (powProd (DensePolySquarefree.sqfDecomp p) 1) p)
    (DensePolySquarefree.sqfDecomp p) 1

/-- **The decomposition identity**: `a/p = poly + Σᵢ Σⱼ aᵢⱼ/dᵢʲ` in `RatFunc R`. -/
theorem sqfPartFrac_ratFunc {p : DensePoly R} (hp : p ≠ 0) (a : DensePoly R) :
    toRatFuncHom a / toRatFuncHom p
      = toRatFuncHom (sqfPartFrac a p).1 + partsSum (sqfPartFrac a p).2 := by
  set L := DensePolySquarefree.sqfDecomp (R := R) p with hL
  have hassoc : Associated p (powProd L 1) := DensePolySquarefree.associated_powProd hp
  have hsf : Squarefree L.prod :=
    squarefree_of_associated (DensePolySquarefree.associated_prod hp)
      (squarefree_sqfreePart hp)
  have hne : ∀ f ∈ L, f ≠ 0 := fun f hf h0 =>
    not_squarefree_zero (h0 ▸ DensePolySquarefree.squarefree_of_mem hf)
  have hw : p * div (powProd L 1) p = powProd L 1 :=
    EuclideanDomain.mul_div_cancel' hp hassoc.dvd
  have hw0 : div (powProd L 1) p ≠ 0 :=
    fun h0 => powProd_ne_zero hne 1 (by rw [← hw, h0, mul_zero])
  have hmain := partFracAux_ratFunc L (a * div (powProd L 1) p) 1 hne hsf
  have hcancel : toRatFuncHom (a * div (powProd L 1) p) / toRatFuncHom (powProd L 1)
      = toRatFuncHom a / toRatFuncHom p := by
    nth_rewrite 2 [← hw]
    rw [map_mul, map_mul]
    exact mul_div_mul_right _ _ (toRatFuncHom_ne_zero hw0)
  rw [sqfPartFrac, ← hL, ← hmain, hcancel]

omit [CharZero R] in
/-- Every numerator of the decomposition is reduced modulo its factor. -/
theorem sqfPartFrac_size_lt {p : DensePoly R} (a : DensePoly R) :
    ∀ fa ∈ (sqfPartFrac a p).2, ∀ b ∈ fa.2, b.size < fa.1.size := by
  refine partFracAux_size_lt _ _ 1 (fun f hf h0 => ?_)
  exact not_squarefree_zero (h0 ▸ DensePolySquarefree.squarefree_of_mem hf)

omit [CharZero R] in
/-- Every factor of the decomposition is squarefree (inherited from the contract). -/
theorem squarefree_of_mem_sqfPartFrac {p : DensePoly R} {a : DensePoly R}
    {fa : DensePoly R × List (DensePoly R)} (hfa : fa ∈ (sqfPartFrac a p).2) :
    Squarefree fa.1 := by
  have hmem : ∀ (L : List (DensePoly R)) (b : DensePoly R) (n : ℕ),
      ∀ x ∈ (partFracAux b L n).2, x.1 ∈ L := by
    intro L
    induction L with
    | nil => intro b n x hx; exact absurd hx (List.not_mem_nil)
    | cons f T ih =>
        intro b n x hx
        simp only [partFracAux] at hx
        rcases List.mem_cons.mp hx with rfl | hx
        · simp
        · exact List.mem_cons_of_mem f (ih _ (n + 1) x hx)
  exact DensePolySquarefree.squarefree_of_mem (hmem _ _ 1 fa hfa)

end DensePoly

end DeepWiki.CAlgebra
