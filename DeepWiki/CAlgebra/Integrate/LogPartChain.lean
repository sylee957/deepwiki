import DeepWiki.CAlgebra.Resultant

/-! # The dispatched bivariate walk

The chain view of the dispatched pseudo-remainder sequence: the ℕ-indexed `z`-primitive
chain `zChain` aligned with `DensePolyPRS.prs`, the bridged per-step identities, and the
`WalkData` bundle collecting the aliveness, size, and bridged chain-relation facts the
subresultant telescope consumes. -/

namespace DeepWiki.CAlgebra

universe u

namespace DensePoly

variable {R : Type u} [Field R] [DecidableEq R] [DensePolyGcd R]

/-- One `z`-primitive pseudo-remainder step. -/
def zStep (f g : DensePoly (DensePoly R)) : DensePoly (DensePoly R) :=
  zPrimitive (pseudoMod f g)

/-- The ℕ-indexed `z`-primitive pseudo-remainder chain — the dispatched bivariate walk in
the shape the subresultant chain theorems consume. -/
def zChain (f g : DensePoly (DensePoly R)) : ℕ → DensePoly (DensePoly R)
  | 0 => f
  | 1 => g
  | l + 2 => zStep (zChain f g l) (zChain f g (l + 1))

/-- `zChain f g 0 = f`: the chain starts at the dividend. -/
@[simp] theorem zChain_zero (f g : DensePoly (DensePoly R)) : zChain f g 0 = f := rfl

/-- `zChain f g 1 = g`: the chain's second element is the divisor. -/
@[simp] theorem zChain_one (f g : DensePoly (DensePoly R)) : zChain f g 1 = g := rfl

/-- The chain recursion: each element is the `z`-step of the previous two. -/
theorem zChain_add_two (f g : DensePoly (DensePoly R)) (l : ℕ) :
    zChain f g (l + 2) = zStep (zChain f g l) (zChain f g (l + 1)) := rfl

/-- Restarting the chain one step in shifts the index. -/
theorem zChain_shift (f g : DensePoly (DensePoly R)) :
    ∀ l, zChain g (zStep f g) (l + 1) = zChain f g (l + 2)
  | 0 => rfl
  | 1 => rfl
  | l + 2 => by
      show zStep (zChain g (zStep f g) (l + 1)) (zChain g (zStep f g) (l + 2)) = _
      rw [zChain_shift f g l, zChain_shift f g (l + 1)]
      rfl

/-- The dispatched bivariate sequence unfolds along the `z`-step. -/
theorem prs_z_eq (f g : DensePoly (DensePoly R)) :
    DensePolyPRS.prs f g
      = if g.size = 0 then [] else g :: DensePolyPRS.prs g (zStep f g) := by
  show prsDescent _ _ _ f g = _
  rcases eq_or_ne g.size 0 with h | h
  · rw [if_pos h, prsDescent, descentTrace_of_size_eq_zero _ _ _ _ _ h, List.map_nil]
  · rw [if_neg h, prsDescent, descentTrace_of_size_ne_zero _ _ _ _ _ h, List.map_cons]
    rfl

/-- Every element of the dispatched sequence is nonzero (the walk stops before appending
a zero divisor). -/
theorem prs_ne_zero (f g : DensePoly (DensePoly R)) :
    ∀ S ∈ DensePolyPRS.prs f g, S ≠ 0 := by
  intro S hS
  induction hd : (DensePolyPRS.prs f g).length generalizing f g with
  | zero =>
      rw [prs_z_eq] at hS hd
      rcases eq_or_ne g.size 0 with h | h
      · rw [if_pos h] at hS; simp at hS
      · rw [if_neg h] at hd; simp at hd
  | succ n ih =>
      rw [prs_z_eq] at hS hd
      rcases eq_or_ne g.size 0 with h | h
      · rw [if_pos h] at hS; simp at hS
      · rw [if_neg h] at hS hd
        rcases List.mem_cons.mp hS with rfl | hS'
        · exact fun h0 => h (by rw [h0, size_zero])
        · exact ih g (zStep f g) hS' (by simpa using hd)

/-- The `k`-th element of the dispatched sequence is the `(k+1)`-st chain element. -/
theorem prs_getElem?_eq_zChain (f g : DensePoly (DensePoly R)) (k : ℕ)
    (S : DensePoly (DensePoly R)) (hS : (DensePolyPRS.prs f g)[k]? = some S) :
    S = zChain f g (k + 1) := by
  induction k generalizing f g with
  | zero =>
      rw [prs_z_eq] at hS
      rcases eq_or_ne g.size 0 with h | h
      · rw [if_pos h] at hS; simp at hS
      · rw [if_neg h] at hS
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hS
        rw [← hS, zChain_one]
  | succ k ih =>
      rw [prs_z_eq] at hS
      rcases eq_or_ne g.size 0 with h | h
      · rw [if_pos h] at hS; simp at hS
      · rw [if_neg h, List.getElem?_cons_succ] at hS
        rw [ih g (zStep f g) hS, zChain_shift]

/-- Every dispatched sequence element is the entry element or a `z`-primitive part. -/
theorem prs_shape_mem (f g : DensePoly (DensePoly R)) (S : DensePoly (DensePoly R))
    (hS : S ∈ DensePolyPRS.prs f g) :
    S = g ∨ ∃ prem : DensePoly (DensePoly R), prem ≠ 0 ∧ S = zPrimitive prem := by
  induction hd : (DensePolyPRS.prs f g).length generalizing f g with
  | zero =>
      rw [prs_z_eq] at hS hd
      rcases eq_or_ne g.size 0 with h | h
      · rw [if_pos h] at hS; simp at hS
      · rw [if_neg h] at hd; simp at hd
  | succ n ih =>
      rw [prs_z_eq] at hS hd
      rcases eq_or_ne g.size 0 with h | h
      · rw [if_pos h] at hS; simp at hS
      · rw [if_neg h] at hS hd
        rcases List.mem_cons.mp hS with rfl | hS'
        · exact Or.inl rfl
        · rcases ih g (zStep f g) hS' (by simpa using hd) with h1 | h1
          · right
            refine ⟨pseudoMod f g, ?_, h1⟩
            intro h0
            apply prs_ne_zero g (zStep f g) S hS'
            rw [h1, zStep, h0, zPrimitive_zero]
          · exact Or.inr h1

/-- The bridged chain element: the `l`-th chain element read through `toPolynomial₂`. -/
noncomputable def walkF (f g : DensePoly (DensePoly R)) (l : ℕ) : Polynomial (Polynomial R) :=
  toPolynomial₂ (zChain f g l)

/-- The bridged pseudo-quotient along the chain. -/
noncomputable def walkQ (f g : DensePoly (DensePoly R)) (l : ℕ) : Polynomial (Polynomial R) :=
  toPolynomial₂ (pseudoDiv (zChain f g l) (zChain f g (l + 1)))

/-- The bridged pseudo-division multiplier along the chain. -/
noncomputable def walkAlpha (f g : DensePoly (DensePoly R)) (l : ℕ) : Polynomial R :=
  toPolynomial ((zChain f g (l + 1)).leadingCoeff
    ^ ((zChain f g l).size + 1 - (zChain f g (l + 1)).size))

/-- The bridged `z`-content of the pseudo-remainder along the chain. -/
noncomputable def walkBeta (f g : DensePoly (DensePoly R)) (l : ℕ) : Polynomial R :=
  toPolynomial (zContent (pseudoMod (zChain f g l) (zChain f g (l + 1))))

/-- The bridged chain starts at the bridged dividend. -/
@[simp] theorem walkF_zero (f g : DensePoly (DensePoly R)) : walkF f g 0 = toPolynomial₂ f :=
  rfl

/-- The bridged chain's second element is the bridged divisor. -/
@[simp] theorem walkF_one (f g : DensePoly (DensePoly R)) : walkF f g 1 = toPolynomial₂ g :=
  rfl

omit [DensePolyGcd R] in
/-- The bridged pseudo-division identity at one walk step. -/
theorem walk_step_identity (f g : DensePoly (DensePoly R)) (hgsz : g.size ≠ 0) :
    toPolynomial₂ (pseudoDiv f g) * toPolynomial₂ g + toPolynomial₂ (pseudoMod f g)
      = Polynomial.C (toPolynomial (g.leadingCoeff ^ (f.size + 1 - g.size)))
        * toPolynomial₂ f := by
  have h0 := congrArg toPolynomial₂Hom (pseudoDivMod_spec (q := g) hgsz f)
  simp only [map_add, map_mul, toPolynomial₂Hom_apply, toPolynomial₂_C] at h0
  exact h0

/-- The bridged chain relation at one walk step, through the `z`-primitive strip. -/
theorem walk_step_rel (f g : DensePoly (DensePoly R)) (hgsz : g.size ≠ 0) :
    Polynomial.C (toPolynomial (g.leadingCoeff ^ (f.size + 1 - g.size))) * toPolynomial₂ f
      = Polynomial.C (toPolynomial (zContent (pseudoMod f g))) * toPolynomial₂ (zStep f g)
        + toPolynomial₂ g * toPolynomial₂ (pseudoDiv f g) := by
  have hlevel : C (g.leadingCoeff ^ (f.size + 1 - g.size)) * f
      = C (zContent (pseudoMod f g)) * zStep f g + g * pseudoDiv f g := by
    rw [zStep, C_zContent_mul_zPrimitive, ← pseudoDivMod_spec (q := g) hgsz f]
    show pseudoDiv _ _ * _ + pseudoMod _ _ = pseudoMod _ _ + _ * pseudoDiv _ _
    ring
  have hbr := congrArg toPolynomial₂Hom hlevel
  simpa only [map_mul, map_add, toPolynomial₂Hom_apply, toPolynomial₂_C] using hbr

omit [DensePolyGcd R] in
/-- The pseudo-quotient degree bound at one walk step, bridged. -/
theorem walk_step_Q_deg (f g : DensePoly (DensePoly R)) (hfg : g.size ≤ f.size)
    (hg0 : g ≠ 0) :
    (toPolynomial₂ (pseudoDiv f g)).natDegree + (toPolynomial₂ g).natDegree
      ≤ (toPolynomial₂ f).natDegree := by
  have hgsz : g.size ≠ 0 := fun h0 => hg0 (eq_zero_of_size_zero h0)
  rcases eq_or_ne (pseudoDiv f g) 0 with hq0 | hq0
  · rw [hq0, toPolynomial₂_zero, Polynomial.natDegree_zero, zero_add,
      natDegree₂_eq_size_sub_one, natDegree₂_eq_size_sub_one]
    omega
  · have h1 := pseudoDiv_natDegree_le hg0 hfg hq0
    rw [natDegree_toPolynomial_eq_size_sub_one] at h1
    rw [natDegree₂_eq_size_sub_one, natDegree₂_eq_size_sub_one,
      natDegree₂_eq_size_sub_one]
    omega

/-- The walk bundle: the aliveness, size, and bridged chain-relation facts of the
dispatched pseudo-remainder walk through index `k`, in the shape the subresultant
telescope consumes. -/
structure WalkData (f g : DensePoly (DensePoly R)) (k : ℕ) : Prop where
  /-- Every chain element through index `k+1` is nonzero. -/
  alive : ∀ j ≤ k, zChain f g (j + 1) ≠ 0
  /-- Each walk step strictly decreases the size. -/
  step_size : ∀ l ≤ k, (zChain f g (l + 2)).size < (zChain f g (l + 1)).size
  /-- The size chain is monotone across any span of steps. -/
  mono : ∀ dlt l, l + dlt ≤ k →
    (zChain f g (l + dlt + 1)).size ≤ (zChain f g (l + 1)).size
  /-- Consecutive chain elements are size-ordered (including the entry pair). -/
  ord : ∀ l ≤ k, (zChain f g (l + 1)).size ≤ (zChain f g l).size
  /-- The bridged chain relation `C α · F l = C β · F (l+2) + F (l+1) · Q l`. -/
  rel : ∀ l ≤ k - 1, Polynomial.C (walkAlpha f g l) * walkF f g l
    = Polynomial.C (walkBeta f g l) * walkF f g (l + 2) + walkF f g (l + 1) * walkQ f g l

namespace WalkData

variable {f g : DensePoly (DensePoly R)} {k : ℕ}

/-- Every chain element through index `k+1` has nonzero size. -/
theorem sizes_ne (w : WalkData f g k) : ∀ j ≤ k, (zChain f g (j + 1)).size ≠ 0 :=
  fun j hj h0 => w.alive j hj (eq_zero_of_size_zero h0)

/-- The pseudo-remainders along the live walk are nonzero (their primitive parts are). -/
theorem prem_ne_zero (w : WalkData f g k) :
    ∀ l, l + 1 ≤ k → pseudoMod (zChain f g l) (zChain f g (l + 1)) ≠ 0 := by
  intro l hl h0
  have := w.alive (l + 1) hl
  rw [zChain_add_two, zStep, h0, zPrimitive_zero] at this
  exact this rfl

/-- The bridged pseudo-division multipliers along the walk are nonzero. -/
theorem alpha_ne_zero (w : WalkData f g k) : ∀ l ≤ k, walkAlpha f g l ≠ 0 :=
  fun l hl => toPolynomial_ne_zero (pow_ne_zero _ (leadingCoeff_ne_zero (w.sizes_ne l hl)))

/-- The bridged `z`-contents along the live walk are nonzero. -/
theorem beta_ne_zero (w : WalkData f g k) : ∀ l, l + 1 ≤ k → walkBeta f g l ≠ 0 :=
  fun l hl => toPolynomial_ne_zero (zContent_ne_zero (w.prem_ne_zero l hl))

/-- The bridged chain elements through index `k+1` are nonzero. -/
theorem F_ne_zero (w : WalkData f g k) : ∀ l ≤ k, walkF f g (l + 1) ≠ 0 :=
  fun l hl => toPolynomial₂_ne_zero (w.alive l hl)

/-- The bridged chain elements have nonzero leading coefficients. -/
theorem F_lc_ne_zero (w : WalkData f g k) :
    ∀ l ≤ k, (walkF f g (l + 1)).coeff (walkF f g (l + 1)).natDegree ≠ 0 :=
  fun l hl => Polynomial.leadingCoeff_ne_zero.mpr (toPolynomial₂_ne_zero (w.alive l hl))

/-- Each walk step strictly decreases the bridged degree. -/
theorem F_deg_step (w : WalkData f g k) :
    ∀ l, l + 1 ≤ k → (walkF f g (l + 2)).natDegree < (walkF f g (l + 1)).natDegree := by
  intro l hl
  simp only [walkF, natDegree₂_eq_size_sub_one]
  have h1 := w.step_size l (by omega)
  have h2 : (zChain f g (l + 2)).size ≠ 0 := w.sizes_ne (l + 1) hl
  omega

/-- The last bridged chain element has strictly smaller degree than every interior
element. -/
theorem F_deg_last_lt (w : WalkData f g k) :
    ∀ l, l + 1 < k → (walkF f g (k + 1)).natDegree < (walkF f g (l + 2)).natDegree := by
  intro l hl
  simp only [walkF, natDegree₂_eq_size_sub_one]
  have h1 : (zChain f g (k + 1)).size ≤ (zChain f g (l + 3)).size := by
    have := w.mono (k - (l + 2)) (l + 2) (by omega)
    rwa [show l + 2 + (k - (l + 2)) + 1 = k + 1 from by omega] at this
  have h2 : (zChain f g (l + 3)).size < (zChain f g (l + 2)).size :=
    w.step_size (l + 1) (by omega)
  have h3 : (zChain f g (k + 1)).size ≠ 0 := w.sizes_ne k le_rfl
  omega

/-- The bridged pseudo-quotient degree bound along the walk. -/
theorem Q_deg_le (w : WalkData f g k) : ∀ l ≤ k,
    (walkQ f g l).natDegree + (walkF f g (l + 1)).natDegree ≤ (walkF f g l).natDegree :=
  fun l hl =>
    walk_step_Q_deg (zChain f g l) (zChain f g (l + 1)) (w.ord l hl) (w.alive l hl)

/-- The walk bundle from a live sequence index: any `k`-th element of the dispatched
sequence certifies the walk through index `k`. -/
theorem ofGetElem? (f g : DensePoly (DensePoly R)) (hfg : g.size ≤ f.size) {k : ℕ}
    {S : DensePoly (DensePoly R)} (hS : (DensePolyPRS.prs f g)[k]? = some S) :
    WalkData f g k := by
  have hlen : k < (DensePolyPRS.prs f g).length := by
    by_contra hlen
    rw [List.getElem?_eq_none (by omega)] at hS
    simp at hS
  have halive : ∀ j, j ≤ k → zChain f g (j + 1) ≠ 0 := by
    intro j hj
    have hj' : j < (DensePolyPRS.prs f g).length := by omega
    have heq := prs_getElem?_eq_zChain f g j ((DensePolyPRS.prs f g)[j])
      (List.getElem?_eq_getElem hj')
    rw [← heq]
    exact prs_ne_zero f g _ (List.getElem_mem hj')
  have hsizes_ne : ∀ j, j ≤ k → (zChain f g (j + 1)).size ≠ 0 := fun j hj h0 =>
    halive j hj (eq_zero_of_size_zero h0)
  have hstep : ∀ l, l ≤ k → (zChain f g (l + 2)).size < (zChain f g (l + 1)).size := by
    intro l hl
    rw [zChain_add_two]
    calc (zStep (zChain f g l) (zChain f g (l + 1))).size
        ≤ (pseudoMod (zChain f g l) (zChain f g (l + 1))).size := zPrimitive_size_le _
      _ < (zChain f g (l + 1)).size := pseudoMod_size_lt (hsizes_ne l hl) _
  have hmono : ∀ dlt l, l + dlt ≤ k →
      (zChain f g (l + dlt + 1)).size ≤ (zChain f g (l + 1)).size := by
    intro dlt
    induction dlt with
    | zero => intro l _; exact le_rfl
    | succ n ihn =>
        intro l hl
        have h1 := ihn l (by omega)
        have h2 := hstep (l + n) (by omega)
        have he : l + (n + 1) + 1 = l + n + 2 := by omega
        rw [he]
        omega
  have hord : ∀ l, l ≤ k → (zChain f g (l + 1)).size ≤ (zChain f g l).size := by
    intro l hl
    rcases l with _ | l'
    · exact hfg
    · exact le_of_lt (hstep l' (by omega))
  refine ⟨halive, hstep, hmono, hord, ?_⟩
  intro l hl
  have h := walk_step_rel (zChain f g l) (zChain f g (l + 1)) (hsizes_ne l (by omega))
  simpa only [walkAlpha, walkBeta, walkF, walkQ, zChain_add_two] using h

end WalkData

end DensePoly

end DeepWiki.CAlgebra
