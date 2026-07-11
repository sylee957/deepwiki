import DeepWiki.ComputableAlgebra.LinearAlgebraRat

/-! # Correctness of the ℚ-Gaussian-elimination linear solver

Abstract correctness over `ℚ` of `crref` (list-based Gauss–Jordan reduction to RREF) and
`cConstSolveUniqueQ` (back-substituted solution): the solution-preserving invariant, the forward
reduced-echelon structure, and the headline `cConstSolveUniqueQ_sound`. -/

namespace DeepWiki.SymbolicIntegration.DensePoly

/-- `getD` of an append, left part (generic). -/
theorem getD_append_left {α : Type*} (l l' : List α) (d : α) (n : ℕ) (hn : n < l.length) :
    (l ++ l').getD n d = l.getD n d := by
  rw [getD_lt_gen _ _ _ (by rw [List.length_append]; omega), getD_lt_gen _ _ _ hn,
    List.getElem_append_left hn]

/-- `getD` of an append, right part (generic). -/
theorem getD_append_right {α : Type*} (l l' : List α) (d : α) (n : ℕ) (hn : l.length ≤ n) :
    (l ++ l').getD n d = l'.getD (n - l.length) d := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_right hn]

/-- Dot product of a row with a vector (zipWith-mul then sum). Truncates to the shorter length. -/
def dotQ (r x : List ℚ) : ℚ := (List.zipWith (· * ·) r x).sum

/-- A vector `x` solves row `r` if `r · x = 0`. -/
def solvesRow (r x : List ℚ) : Prop := dotQ r x = 0

/-- A vector solves every row in a list. -/
def solvesAll (rows : List (List ℚ)) (x : List ℚ) : Prop := ∀ r ∈ rows, solvesRow r x

/-- Every vector solves the empty row system. -/
theorem solvesAll_nil (x : List ℚ) : solvesAll [] x := by intro r hr; simp at hr

/-- Solving a cons row system is solving its head row and tail system. -/
theorem solvesAll_cons {r : List ℚ} {rows : List (List ℚ)} {x : List ℚ} :
    solvesAll (r :: rows) x ↔ solvesRow r x ∧ solvesAll rows x := by
  constructor
  · intro h; exact ⟨h r (by simp), fun s hs => h s (by simp [hs])⟩
  · intro ⟨h1, h2⟩ s hs; rcases List.mem_cons.mp hs with rfl | hs'; exact h1; exact h2 s hs'

/-- dotQ is linear in the scaling of the row: `dotQ (r.map (c * ·)) x = c * dotQ r x`. -/
theorem dotQ_map_scale (c : ℚ) (r x : List ℚ) :
    dotQ (r.map (c * ·)) x = c * dotQ r x := by
  unfold dotQ
  induction r generalizing x with
  | nil => simp
  | cons a as ih =>
    cases x with
    | nil => simp
    | cons b bs => simp [List.zipWith_cons_cons, ih]; ring

/-- The elimination dot identity: when both `r` and `prn` are at least as long as `x`,
`dotQ (zipWith (ri - f*pi) r prn) x = dotQ r x - f * dotQ prn x`. -/
theorem dotQ_zipWith_sub (f : ℚ) (r prn x : List ℚ)
    (hr : x.length ≤ r.length) (hp : x.length ≤ prn.length) :
    dotQ (List.zipWith (fun ri pi => ri - f * pi) r prn) x
      = dotQ r x - f * dotQ prn x := by
  unfold dotQ
  induction x generalizing r prn with
  | nil => simp
  | cons xa xs ih =>
    cases r with
    | nil => simp at hr
    | cons ra rs =>
      cases prn with
      | nil => simp at hp
      | cons pa ps =>
        simp only [List.zipWith_cons_cons, List.sum_cons]
        rw [ih rs ps (by simpa using hr) (by simpa using hp)]
        ring

/-- The length of `zipWith` is the min of the two lengths. -/
theorem length_zipWith_elim (f : ℚ) (r prn : List ℚ) :
    (List.zipWith (fun ri pi => ri - f * pi) r prn).length = min r.length prn.length :=
  List.length_zipWith

/-- A row that is zero on every column `< v.length` is killed by `v`: `dotQ r v = 0`. -/
theorem dotQ_eq_zero_of_cleared (r v : List ℚ)
    (h : ∀ c, c < v.length → r.getD c 0 = 0) : dotQ r v = 0 := by
  unfold dotQ
  induction r generalizing v with
  | nil => simp
  | cons a as ih =>
    cases v with
    | nil => simp
    | cons b bs =>
      simp only [List.zipWith_cons_cons, List.sum_cons]
      have ha : a = 0 := by
        have := h 0 (by simp); simpa using this
      rw [ha, zero_mul, zero_add]
      apply ih
      intro c hc
      have := h (c + 1) (by simpa using hc)
      simpa using this

/-- `getD` of a `zipWith`-elim row at column `c`, when `c < min`: it is the subtraction. -/
theorem getD_zipWith_elim (f : ℚ) (r prn : List ℚ) (c : ℕ)
    (hr : c < r.length) (hp : c < prn.length) :
    (List.zipWith (fun ri pi => ri - f * pi) r prn).getD c 0
      = r.getD c 0 - f * prn.getD c 0 := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_zipWith]
  rw [List.getElem?_eq_getElem hr, List.getElem?_eq_getElem hp]
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hr, List.getElem?_eq_getElem hp]

/-- `solvesRow` of a scaled (normalized) pivot row: `solvesRow (pr.map (·/piv)) x ↔ solvesRow pr x`
when `piv ≠ 0`. (`pr.map (·/piv) = pr.map ((1/piv) * ·)`, dotQ scales by `1/piv ≠ 0`.) -/
theorem solvesRow_map_div (piv : ℚ) (hpiv : piv ≠ 0) (pr x : List ℚ) :
    solvesRow (pr.map (· / piv)) x ↔ solvesRow pr x := by
  unfold solvesRow
  have hmap : (pr.map (· / piv)) = pr.map ((1 / piv) * ·) := by
    apply List.map_congr_left; intro a _; field_simp
  rw [hmap, dotQ_map_scale]
  have hinv : (1 / piv) ≠ 0 := by simp [hpiv]
  rw [mul_eq_zero]
  constructor
  · rintro (h' | h')
    · exact absurd h' hinv
    · exact h'
  · intro h; exact Or.inr h

/-- Soundness of `crref.go`: any `v` solving the output RREF rows also solves every `rest` and
`pivRows` row (under the length and cleared-below-`col` invariants). -/
theorem crref_go_solves (ncols : ℕ) (v : List ℚ) (hv : v.length ≤ ncols) :
    ∀ (fuel col : ℕ) (rest pivRows : List (List ℚ)) (pivCols : List ℕ),
      ncols ≤ fuel + col →
      (∀ r ∈ rest ++ pivRows, v.length ≤ r.length) →
      (∀ r ∈ rest, ∀ c, c < col → r.getD c 0 = 0) →
      solvesAll (crref.go ncols fuel col rest pivRows pivCols).1 v →
      solvesAll rest v ∧ solvesAll pivRows v := by
  intro fuel
  induction fuel with
  | zero =>
    intro col rest pivRows pivCols hfuel hlen hcl hsolveR
    -- fuel = 0: returns pivRows.reverse. hfuel ⟹ ncols ≤ col ⟹ v.length ≤ col, so the dropped
    -- rest rows are cleared below v.length and hence killed by v.
    simp only [Nat.zero_add] at hfuel
    rw [crref.go] at hsolveR
    refine ⟨fun r hr => ?_, ?_⟩
    · exact dotQ_eq_zero_of_cleared r v (fun c hc => hcl r hr c (lt_of_lt_of_le hc (le_trans hv hfuel)))
    · -- solvesAll pivRows v from solvesAll pivRows.reverse v
      intro r hr
      exact hsolveR r (by simpa using hr)
  | succ f ih =>
    intro col rest pivRows pivCols hfuel hlen hcl hsolveR
    cases rest with
    | nil =>
      -- rest = []: returns pivRows.reverse; solvesAll [] trivial, pivRows from reverse.
      rw [crref.go] at hsolveR
      · refine ⟨solvesAll_nil v, fun r hr => hsolveR r (by simpa using hr)⟩
      · nofun
    | cons r0 rs =>
      -- rest = r0 :: rs nonempty: enter the fuel+1 branch.
      rw [crref.go] at hsolveR
      rotate_left
      · nofun
      by_cases hcol : col ≥ ncols
      · -- col ≥ ncols exit: returns pivRows.reverse, drops (r0::rs), each cleared below col ≥ v.length.
        rw [if_pos hcol] at hsolveR
        refine ⟨fun r hr => ?_, fun r hr => hsolveR r (by simpa using hr)⟩
        exact dotQ_eq_zero_of_cleared r v
          (fun c hc => hcl r hr c (lt_of_lt_of_le hc (le_trans hv hcol)))
      · rw [if_neg hcol] at hsolveR
        rw [not_le] at hcol
        cases hfind : (r0 :: rs).find? (fun r => decide ((r.getD col 0) ≠ 0)) with
        | none =>
          -- free column: rest unchanged, col → col+1; find?=none ⟹ every rest row is 0 at col.
          rw [hfind] at hsolveR
          have hcl' : ∀ r ∈ (r0 :: rs), ∀ c, c < col + 1 → r.getD c 0 = 0 := by
            intro r hr c hc
            rcases Nat.lt_succ_iff_lt_or_eq.mp hc with hc' | rfl
            · exact hcl r hr c hc'
            · have := List.find?_eq_none.mp hfind r hr
              simpa using this
          exact ih (col + 1) (r0 :: rs) pivRows pivCols (by omega) hlen hcl' hsolveR
        | some pr =>
          rw [hfind] at hsolveR
          -- pivot pr ∈ rest, nonzero at col.
          have hprmem : pr ∈ (r0 :: rs) := List.mem_of_find?_eq_some hfind
          have hprnz : (pr.getD col 0) ≠ 0 := by
            have := List.find?_some hfind
            simpa using this
          set piv : ℚ := pr.getD col 0 with hpivdef
          -- col is within pr's length (else getD would be the default 0).
          have hcolpr : col < pr.length := by
            by_contra hc
            exact hprnz (getD_long_gen pr col 0 (by omega))
          have hvpr : v.length ≤ pr.length := hlen pr (List.mem_append_left _ hprmem)
          -- the normalized pivot row and its key facts.
          set prn : List ℚ := pr.map (· / piv) with hprndef
          have hprnlen : prn.length = pr.length := by rw [hprndef, List.length_map]
          have hvprn : v.length ≤ prn.length := by rw [hprnlen]; exact hvpr
          have hprn_col : prn.getD col 0 = 1 := by
            rw [hprndef, List.getD_eq_getElem?_getD, List.getElem?_map,
              List.getElem?_eq_getElem hcolpr]
            simp only [Option.map_some, Option.getD_some]
            rw [← getD_lt_gen pr col 0 hcolpr]
            rw [show pr.getD col 0 = piv from hpivdef.symm]
            field_simp
          -- the elimination function used by the def.
          set elim : List ℚ → List ℚ :=
            (fun r => List.zipWith (fun ri pi => ri - (r.getD col 0) * pi) r prn) with helimdef
          -- length of elim r is ≥ v.length when r is long enough.
          have helim_len : ∀ r, v.length ≤ r.length → v.length ≤ (elim r).length := by
            intro r hr; rw [helimdef]; simp only [List.length_zipWith]; omega
          -- dotQ identity for elim r.
          have helim_dot : ∀ r, v.length ≤ r.length →
              dotQ (elim r) v = dotQ r v - (r.getD col 0) * dotQ prn v := by
            intro r hr; rw [helimdef]; exact dotQ_zipWith_sub _ r prn v hr hvprn
          set restElim : List (List ℚ) :=
            ((r0 :: rs).filter (fun r => !decide (r = pr))).map elim with hrestElimdef
          set pivRowsElim : List (List ℚ) := pivRows.map elim with hpivElimdef
          -- length invariant for the recursive call.
          have hlen' : ∀ r ∈ restElim ++ (prn :: pivRowsElim), v.length ≤ r.length := by
            intro r hr
            rw [List.mem_append] at hr
            rcases hr with hr | hr
            · rw [hrestElimdef, List.mem_map] at hr
              obtain ⟨s, hs, rfl⟩ := hr
              rw [List.mem_filter] at hs
              exact helim_len s (hlen s (List.mem_append_left _ hs.1))
            · rcases List.mem_cons.mp hr with rfl | hr
              · exact hvprn
              · rw [hpivElimdef, List.mem_map] at hr
                obtain ⟨s, hs, rfl⟩ := hr
                exact helim_len s (hlen s (List.mem_append_right _ hs))
          -- cleared invariant for the recursive call (rest rows zero below col+1 after elim).
          have hcl' : ∀ r ∈ restElim, ∀ c, c < col + 1 → r.getD c 0 = 0 := by
            intro r hr c hc
            rw [hrestElimdef, List.mem_map] at hr
            obtain ⟨s, hs, rfl⟩ := hr
            rw [List.mem_filter] at hs
            have hsmem : s ∈ (r0 :: rs) := hs.1
            have hslen : v.length ≤ s.length := hlen s (List.mem_append_left _ hsmem)
            -- getD of elim s at c.
            by_cases hc_s : c < s.length
            · by_cases hc_prn : c < prn.length
              · rw [helimdef, getD_zipWith_elim _ s prn c hc_s hc_prn]
                rcases Nat.lt_succ_iff_lt_or_eq.mp hc with hc' | rfl
                · -- c < col: both s and pr cleared, prn cleared.
                  have hs0 : s.getD c 0 = 0 := hcl s hsmem c hc'
                  have hpr0 : pr.getD c 0 = 0 := hcl pr hprmem c hc'
                  have hprn0 : prn.getD c 0 = 0 := by
                    rw [hprndef, List.getD_eq_getElem?_getD, List.getElem?_map]
                    by_cases hcpr : c < pr.length
                    · rw [List.getElem?_eq_getElem hcpr]
                      simp only [Option.map_some, Option.getD_some]
                      have : pr[c] = (0 : ℚ) := by rw [← getD_lt_gen pr c 0 hcpr]; exact hpr0
                      rw [this]; simp
                    · rw [List.getElem?_eq_none_iff.mpr (by omega)]; simp
                  rw [hs0, hprn0]; ring
                · -- c = col: elim zeros the pivot column. s.getD col - (s.getD col)*prn.getD col,
                  -- prn.getD col = 1.
                  rw [hprn_col]; ring
              · -- c ≥ prn.length ≥ col+1 > c contradiction handled: prn.length = pr.length > col
                exfalso; rw [hprnlen] at hc_prn; omega
            · -- c ≥ s.length: elim s also short, getD default 0.
              rw [helimdef]
              exact getD_long_gen _ c 0 (by simp only [List.length_zipWith]; omega)
          -- apply the inductive hypothesis on the reduced system.
          have hrec := ih (col + 1) restElim (prn :: pivRowsElim) (col :: pivCols)
            (by omega) hlen' hcl' hsolveR
          obtain ⟨hRest, hPiv⟩ := hrec
          rw [solvesAll_cons] at hPiv
          obtain ⟨hprn_solve, hpivElim_solve⟩ := hPiv
          -- recover solvesRow pr v from solvesRow prn v.
          have hpr_solve : solvesRow pr v := (solvesRow_map_div piv hprnz pr v).mp hprn_solve
          have hprn_dot0 : dotQ prn v = 0 := hprn_solve
          -- recovery of an original row from its elim image.
          have recover : ∀ s, v.length ≤ s.length → solvesRow (elim s) v → solvesRow s v := by
            intro s hslen hes
            have hd := helim_dot s hslen
            unfold solvesRow at hes ⊢
            rw [hes, hprn_dot0, mul_zero, sub_zero] at hd
            exact hd.symm
          refine ⟨fun r hr => ?_, fun r hr => ?_⟩
          · -- solvesAll (r0::rs) v
            by_cases hrpr : r = pr
            · rw [hrpr]; exact hpr_solve
            · have hrf : r ∈ (r0 :: rs).filter (fun r => !decide (r = pr)) := by
                rw [List.mem_filter]; exact ⟨hr, by simp [hrpr]⟩
              have helimmem : elim r ∈ restElim := by
                rw [hrestElimdef]; exact List.mem_map_of_mem hrf
              exact recover r (hlen r (List.mem_append_left _ hr)) (hRest (elim r) helimmem)
          · -- solvesAll pivRows v
            have helimmem : elim r ∈ pivRowsElim := by
              rw [hpivElimdef]; exact List.mem_map_of_mem hr
            exact recover r (hlen r (List.mem_append_right _ hr)) (hpivElim_solve (elim r) helimmem)

/-- Soundness of `crref`: if `v` solves every row of the RREF `(crref rows ncols).1`, then `v` solves
every input row. -/
theorem crref_solves (rows : List (List ℚ)) (ncols : ℕ) (v : List ℚ)
    (hv : v.length ≤ ncols) (hrows : ∀ r ∈ rows, v.length ≤ r.length)
    (hsol : solvesAll (crref rows ncols).1 v) :
    solvesAll rows v := by
  have h := crref_go_solves ncols v hv (ncols + rows.length + 1) 0 rows [] []
    (by omega) (by simpa using hrows) (by simp) hsol
  exact h.1

/-- The output pivot-column list of `crref.go` is `Nodup` with every entry `< ncols`. -/
theorem crref_go_pivots (ncols : ℕ) :
    ∀ (fuel col : ℕ) (rest pivRows : List (List ℚ)) (pivCols : List ℕ),
      col ≤ ncols →
      (∀ c ∈ pivCols, c < col) →
      pivCols.Nodup →
      (∀ c ∈ (crref.go ncols fuel col rest pivRows pivCols).2, c < ncols) ∧
        (crref.go ncols fuel col rest pivRows pivCols).2.Nodup := by
  intro fuel
  induction fuel with
  | zero =>
    intro col rest pivRows pivCols hcol hpc hnd
    rw [crref.go]
    exact ⟨fun c hc => lt_of_lt_of_le (hpc c (by simpa using hc)) hcol, by simpa using hnd⟩
  | succ f ih =>
    intro col rest pivRows pivCols hcol hpc hnd
    cases rest with
    | nil =>
      rw [crref.go]
      · exact ⟨fun c hc => lt_of_lt_of_le (hpc c (by simpa using hc)) hcol, by simpa using hnd⟩
      · nofun
    | cons r0 rs =>
      rw [crref.go]
      rotate_left
      · nofun
      by_cases hcoln : col ≥ ncols
      · rw [if_pos hcoln]
        exact ⟨fun c hc => lt_of_lt_of_le (hpc c (by simpa using hc)) hcol, by simpa using hnd⟩
      · rw [if_neg hcoln]
        rw [not_le] at hcoln
        cases hfind : (r0 :: rs).find? (fun r => decide ((r.getD col 0) ≠ 0)) with
        | none =>
          exact ih (col + 1) (r0 :: rs) pivRows pivCols (by omega)
            (fun c hc => lt_trans (hpc c hc) (by omega)) hnd
        | some pr =>
          refine ih (col + 1) _ (_ :: _) (col :: pivCols) (by omega) ?_ ?_
          · intro c hc
            rcases List.mem_cons.mp hc with rfl | hc'
            · omega
            · exact lt_trans (hpc c hc') (by omega)
          · rw [List.nodup_cons]
            exact ⟨fun hmem => absurd (hpc col hmem) (lt_irrefl col), hnd⟩

/-- A `Nodup` ℕ-list with all entries `< ncols` and length `≥ ncols` contains every `j < ncols`. -/
theorem mem_of_nodup_bounded_length (PC : List ℕ) (ncols : ℕ)
    (hnd : PC.Nodup) (hb : ∀ c ∈ PC, c < ncols) (hlen : ncols ≤ PC.length)
    (j : ℕ) (hj : j < ncols) : j ∈ PC := by
  have hsub : PC.toFinset ⊆ Finset.range ncols := by
    intro c hc
    rw [List.mem_toFinset] at hc
    rw [Finset.mem_range]; exact hb c hc
  have hcard : (Finset.range ncols).card ≤ PC.toFinset.card := by
    rw [Finset.card_range, List.toFinset_card_of_nodup hnd]; exact hlen
  have heq : PC.toFinset = Finset.range ncols :=
    Finset.eq_of_subset_of_card_le hsub hcard
  have : j ∈ PC.toFinset := by rw [heq, Finset.mem_range]; exact hj
  rwa [List.mem_toFinset] at this

/-- `getD` within range is a member of the list. -/
theorem getD_mem_lt {α : Type*} (l : List α) (m : ℕ) (d : α) (hm : m < l.length) :
    l.getD m d ∈ l := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hm]
  exact List.getElem_mem hm

/-- `getD` of a mapped list within range: `(l.map f).getD m d = f (l.getD m d')` (for `m < l.length`),
specialized to `d = f d'`. We only need the within-range reading. -/
theorem getD_map_lt {α β : Type*} (f : α → β) (l : List α) (m : ℕ) (d : α) (db : β)
    (hm : m < l.length) : (l.map f).getD m db = f (l.getD m d) := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hm,
    List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hm]
  rfl

/-- The reduced-echelon "identity pivot submatrix" property of a `(rows, cols)` pair (rows = pivot
rows, cols = matching pivot columns): the pivot of row `i` read at the pivot column of row `j` is
`1` if `i = j`, else `0`. -/
def isIdentitySubmatrix (rows : List (List ℚ)) (cols : List ℕ) : Prop :=
  rows.length = cols.length ∧
    ∀ i j, i < rows.length → j < cols.length →
      (rows.getD i []).getD (cols.getD j 0) 0 = if i = j then 1 else 0

/-- `getD` of a reversed list reindexes: `l.reverse.getD i d = l.getD (l.length - 1 - i) d` for
`i < l.length`. -/
theorem getD_reverse_lt {α : Type*} (l : List α) (d : α) (i : ℕ) (hi : i < l.length) :
    l.reverse.getD i d = l.getD (l.length - 1 - i) d := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
  rw [List.getElem?_reverse hi]

/-- Joint reversal preserves the identity-submatrix property. -/
theorem isIdentitySubmatrix_reverse (rows : List (List ℚ)) (cols : List ℕ)
    (h : isIdentitySubmatrix rows cols) :
    isIdentitySubmatrix rows.reverse cols.reverse := by
  obtain ⟨hlen, hid⟩ := h
  refine ⟨by simp [hlen], fun i j hi hj => ?_⟩
  rw [List.length_reverse] at hi hj
  rw [getD_reverse_lt rows [] i hi, getD_reverse_lt cols 0 j hj]
  rw [hid (rows.length - 1 - i) (cols.length - 1 - j) (by omega) (by omega)]
  have : (rows.length - 1 - i = cols.length - 1 - j) ↔ (i = j) := by rw [hlen]; omega
  simp only [this]

/-- Forward RREF structure of `crref.go`: the output `(R, PC)` satisfies `isIdentitySubmatrix R PC`. -/
theorem crref_go_rref (ncols : ℕ) :
    ∀ (fuel col : ℕ) (rest pivRows : List (List ℚ)) (pivCols : List ℕ),
      (∀ r ∈ rest ++ pivRows, ncols ≤ r.length) →
      (∀ r ∈ rest, ∀ c, c < col → r.getD c 0 = 0) →
      (∀ j, j < pivCols.length → pivCols.getD j 0 < col) →
      isIdentitySubmatrix pivRows pivCols →
      isIdentitySubmatrix (crref.go ncols fuel col rest pivRows pivCols).1
        (crref.go ncols fuel col rest pivRows pivCols).2 := by
  intro fuel
  induction fuel with
  | zero =>
    intro col rest pivRows pivCols hrl hcl hpc hid
    rw [crref.go]
    exact isIdentitySubmatrix_reverse pivRows pivCols hid
  | succ f ih =>
    intro col rest pivRows pivCols hrl hcl hpc hid
    cases rest with
    | nil =>
      rw [crref.go]
      · exact isIdentitySubmatrix_reverse pivRows pivCols hid
      · nofun
    | cons r0 rs =>
      rw [crref.go]
      rotate_left
      · nofun
      by_cases hcol : col ≥ ncols
      · rw [if_pos hcol]
        exact isIdentitySubmatrix_reverse pivRows pivCols hid
      · rw [if_neg hcol]
        rw [not_le] at hcol
        cases hfind : (r0 :: rs).find? (fun r => decide ((r.getD col 0) ≠ 0)) with
        | none =>
          have hcl' : ∀ r ∈ (r0 :: rs), ∀ c, c < col + 1 → r.getD c 0 = 0 := by
            intro r hr c hc
            rcases Nat.lt_succ_iff_lt_or_eq.mp hc with hc' | rfl
            · exact hcl r hr c hc'
            · have := List.find?_eq_none.mp hfind r hr
              simpa using this
          exact ih (col + 1) (r0 :: rs) pivRows pivCols hrl hcl'
            (fun j hj => lt_trans (hpc j hj) (by omega)) hid
        | some pr =>
          have hprmem : pr ∈ (r0 :: rs) := List.mem_of_find?_eq_some hfind
          have hprnz : (pr.getD col 0) ≠ 0 := by
            have := List.find?_some hfind; simpa using this
          set piv : ℚ := pr.getD col 0 with hpivdef
          have hcolpr : col < pr.length := by
            by_contra hc; exact hprnz (getD_long_gen pr col 0 (by omega))
          set prn : List ℚ := pr.map (· / piv) with hprndef
          have hprnlen : prn.length = pr.length := by rw [hprndef, List.length_map]
          have hprn_col : prn.getD col 0 = 1 := by
            rw [hprndef, List.getD_eq_getElem?_getD, List.getElem?_map,
              List.getElem?_eq_getElem hcolpr]
            simp only [Option.map_some, Option.getD_some]
            rw [← getD_lt_gen pr col 0 hcolpr, show pr.getD col 0 = piv from hpivdef.symm]
            field_simp
          -- prn is cleared below col (pr ∈ rest cleared, scaling preserves zeros).
          have hprn_cleared : ∀ c, c < col → prn.getD c 0 = 0 := by
            intro c hc
            have hpr0 : pr.getD c 0 = 0 := hcl pr hprmem c hc
            rw [hprndef, List.getD_eq_getElem?_getD, List.getElem?_map]
            by_cases hcpr : c < pr.length
            · rw [List.getElem?_eq_getElem hcpr]
              simp only [Option.map_some, Option.getD_some]
              have : pr[c] = (0 : ℚ) := by rw [← getD_lt_gen pr c 0 hcpr]; exact hpr0
              rw [this]; simp
            · rw [List.getElem?_eq_none_iff.mpr (by omega)]; simp
          set elim : List ℚ → List ℚ :=
            (fun r => List.zipWith (fun ri pi => ri - (r.getD col 0) * pi) r prn) with helimdef
          set restElim : List (List ℚ) :=
            ((r0 :: rs).filter (fun r => !decide (r = pr))).map elim with hrestElimdef
          set pivRowsElim : List (List ℚ) := pivRows.map elim with hpivElimdef
          -- lengths: pr ≥ ncols, prn = |pr| ≥ ncols; elim r ≥ ncols.
          have hncolspr : ncols ≤ pr.length := hrl pr (List.mem_append_left _ hprmem)
          have hncolsprn : ncols ≤ prn.length := by rw [hprnlen]; exact hncolspr
          have helim_len : ∀ r, ncols ≤ r.length → ncols ≤ (elim r).length := by
            intro r hr; rw [helimdef]; simp only [List.length_zipWith]; omega
          have hrl' : ∀ r ∈ restElim ++ (prn :: pivRowsElim), ncols ≤ r.length := by
            intro r hr
            rw [List.mem_append] at hr
            rcases hr with hr | hr
            · rw [hrestElimdef, List.mem_map] at hr
              obtain ⟨s, hs, rfl⟩ := hr
              rw [List.mem_filter] at hs
              exact helim_len s (hrl s (List.mem_append_left _ hs.1))
            · rcases List.mem_cons.mp hr with rfl | hr
              · exact hncolsprn
              · rw [hpivElimdef, List.mem_map] at hr
                obtain ⟨s, hs, rfl⟩ := hr
                exact helim_len s (hrl s (List.mem_append_right _ hs))
          -- cleared invariant for restElim (same elimination as the soundness proof).
          have hcl' : ∀ r ∈ restElim, ∀ c, c < col + 1 → r.getD c 0 = 0 := by
            intro r hr c hc
            rw [hrestElimdef, List.mem_map] at hr
            obtain ⟨s, hs, rfl⟩ := hr
            rw [List.mem_filter] at hs
            have hsmem : s ∈ (r0 :: rs) := hs.1
            have hsncols : ncols ≤ s.length := hrl s (List.mem_append_left _ hsmem)
            by_cases hc_s : c < s.length
            · rw [helimdef, getD_zipWith_elim _ s prn c hc_s (by omega)]
              rcases Nat.lt_succ_iff_lt_or_eq.mp hc with hc' | rfl
              · rw [hcl s hsmem c hc', hprn_cleared c hc']; ring
              · rw [hprn_col]; ring
            · rw [helimdef]
              exact getD_long_gen _ c 0 (by simp only [List.length_zipWith]; omega)
          -- pivot-column bound for the new accumulator.
          have hpc' : ∀ j, j < (col :: pivCols).length → (col :: pivCols).getD j 0 < col + 1 := by
            intro j hj
            cases j with
            | zero => simp
            | succ k =>
              simp only [List.getD_cons_succ]
              have hk : k < pivCols.length := by simpa using hj
              exact lt_trans (hpc k hk) (by omega)
          -- ★ the identity-submatrix property of the new accumulator.
          have hid' : isIdentitySubmatrix (prn :: pivRowsElim) (col :: pivCols) := by
            obtain ⟨hidlen, hidval⟩ := hid
            refine ⟨by simp [hpivElimdef, hidlen], fun i j hi hj => ?_⟩
            have hpivElim_len : pivRowsElim.length = pivRows.length := by
              rw [hpivElimdef, List.length_map]
            cases i with
            | zero =>
              cases j with
              | zero => simpa using hprn_col
              | succ k =>
                simp only [List.getD_cons_zero, List.getD_cons_succ]
                have hk : k < pivCols.length := by simpa using hj
                rw [hprn_cleared (pivCols.getD k 0) (hpc k hk)]
                simp
            | succ m =>
              have hm : m < pivRows.length := by
                simp only [List.length_cons, hpivElim_len] at hi; omega
              cases j with
              | zero =>
                simp only [List.getD_cons_succ, List.getD_cons_zero]
                rw [hpivElimdef, getD_map_lt elim pivRows m [] [] hm]
                rw [helimdef, getD_zipWith_elim _ (pivRows.getD m []) prn col
                  (by
                    have := hrl (pivRows.getD m []) (List.mem_append_right _ (getD_mem_lt pivRows m [] hm))
                    omega)
                  (by omega)]
                rw [hprn_col, if_neg (Nat.succ_ne_zero m)]; ring
              | succ k =>
                simp only [List.getD_cons_succ]
                have hk : k < pivCols.length := by simpa using hj
                rw [hpivElimdef, getD_map_lt elim pivRows m [] [] hm]
                have hcltcol : pivCols.getD k 0 < col := hpc k hk
                have hcrow : pivCols.getD k 0 < (pivRows.getD m []).length := by
                  have hrm : ncols ≤ (pivRows.getD m []).length :=
                    hrl (pivRows.getD m []) (List.mem_append_right _ (getD_mem_lt pivRows m [] hm))
                  omega
                rw [helimdef, getD_zipWith_elim _ (pivRows.getD m []) prn (pivCols.getD k 0)
                  hcrow (by omega)]
                rw [hprn_cleared (pivCols.getD k 0) hcltcol, mul_zero, sub_zero]
                rw [hidval m k hm hk]
                simp
          exact ih (col + 1) restElim (prn :: pivRowsElim) (col :: pivCols) hrl' hcl' hpc' hid'

/-- `dotQ` as a `Finset.range` sum over the columns of `v` (when `r` is at least as long as `v`). -/
theorem dotQ_eq_sum (r v : List ℚ) (h : v.length ≤ r.length) :
    dotQ r v = ∑ c ∈ Finset.range v.length, r.getD c 0 * v.getD c 0 := by
  unfold dotQ
  induction v generalizing r with
  | nil => simp
  | cons a as ih =>
    cases r with
    | nil => simp at h
    | cons b bs =>
      rw [List.length_cons, Finset.sum_range_succ']
      simp only [List.zipWith_cons_cons, List.sum_cons, List.getD_cons_succ, List.getD_cons_zero]
      rw [ih bs (by simpa using h), add_comm]

/-- For a member `c` of a list, `idxOf?` returns `some` of its `idxOf`. -/
theorem idxOf?_of_mem {α : Type*} [BEq α] [LawfulBEq α] (l : List α) (c : α) (hc : c ∈ l) :
    l.idxOf? c = some (l.idxOf c) := by
  have hlt : l.idxOf c < l.length := List.idxOf_lt_length_of_mem hc
  rw [List.idxOf_eq_getD_idxOf?] at hlt ⊢
  cases h : l.idxOf? c with
  | none => rw [h] at hlt; simp at hlt
  | some i => rfl

/-- Top-level `crref` correctness: the RREF `(R, PC)` has an identity pivot submatrix, `PC` is `Nodup`,
and every pivot column is `< ncols`. -/
theorem crref_rref (rows : List (List ℚ)) (ncols : ℕ)
    (hrows : ∀ r ∈ rows, ncols ≤ r.length) :
    isIdentitySubmatrix (crref rows ncols).1 (crref rows ncols).2 ∧
      (crref rows ncols).2.Nodup ∧ (∀ c ∈ (crref rows ncols).2, c < ncols) := by
  refine ⟨crref_go_rref ncols (ncols + rows.length + 1) 0 rows [] []
      (by simpa using hrows) (by simp) (by simp) ⟨rfl, by intro i j hi hj; simp at hi⟩, ?_, ?_⟩
  · exact (crref_go_pivots ncols (ncols + rows.length + 1) 0 rows [] []
      (by omega) (by simp) (by simp)).2
  · exact (crref_go_pivots ncols (ncols + rows.length + 1) 0 rows [] []
      (by omega) (by simp) (by simp)).1

/-- The back-read of a full-rank RREF solves the RREF rows: the back-substituted vector `x` (with last
coordinate `-1`) solves every row of `R`. -/
theorem back_read_solves_rref (R : List (List ℚ)) (PC : List ℕ) (ncols : ℕ)
    (hid : isIdentitySubmatrix R PC) (hnd : PC.Nodup) (hpcb : ∀ c ∈ PC, c < ncols)
    (hrank : ncols ≤ PC.length) (hrlen : ∀ r ∈ R, ncols + 1 ≤ r.length) :
    let x : List ℚ := (List.range ncols).map (fun j =>
      match PC.idxOf? j with | some pr => (R.getD pr []).getD ncols 0 | none => 0)
    solvesAll R (x ++ [(-1 : ℚ)]) := by
  obtain ⟨hRPClen, hidval⟩ := hid
  -- PC.length = ncols (nodup, all < ncols, and ≥ ncols).
  have hPClen : PC.length = ncols := by
    have hsub : PC.toFinset ⊆ Finset.range ncols := by
      intro c hc; rw [List.mem_toFinset] at hc; rw [Finset.mem_range]; exact hpcb c hc
    have := Finset.card_le_card hsub
    rw [List.toFinset_card_of_nodup hnd, Finset.card_range] at this
    omega
  intro x r hr
  -- r is R.getD i [] for some i < R.length.
  obtain ⟨i, hi, hri⟩ := List.getElem_of_mem hr
  rw [show r = R.getD i [] by rw [getD_lt_gen R i [] hi, hri]]
  -- length facts.
  have hRlen_i : ncols + 1 ≤ (R.getD i []).length := hrlen _ (getD_mem_lt R i [] hi)
  have hxlen : x.length = ncols := by simp [x]
  have hvlen : (x ++ [(-1 : ℚ)]).length = ncols + 1 := by simp [hxlen]
  unfold solvesRow
  rw [dotQ_eq_sum (R.getD i []) (x ++ [(-1 : ℚ)]) (by rw [hvlen]; omega)]
  rw [hvlen, Finset.sum_range_succ]
  -- the rhs-column term: v[ncols] = -1.
  have hvncols : (x ++ [(-1 : ℚ)]).getD ncols 0 = -1 := by
    rw [getD_append_right _ _ _ _ (by rw [hxlen]), hxlen]; simp
  rw [hvncols]
  -- the main sum over the variable columns, reindexed by the pivot bijection.
  have hmain : (∑ c ∈ Finset.range ncols, (R.getD i []).getD c 0 * (x ++ [(-1:ℚ)]).getD c 0)
      = (R.getD i []).getD ncols 0 := by
    -- reindex c = PC[j].
    have hbij : (∑ c ∈ Finset.range ncols, (R.getD i []).getD c 0 * (x ++ [(-1:ℚ)]).getD c 0)
        = ∑ j ∈ Finset.range PC.length,
            (R.getD i []).getD (PC.getD j 0) 0 * (x ++ [(-1:ℚ)]).getD (PC.getD j 0) 0 := by
      apply Finset.sum_nbij' (fun c => PC.idxOf c) (fun j => PC.getD j 0)
      · intro c hc
        rw [Finset.mem_range] at hc ⊢
        exact List.idxOf_lt_length_of_mem (mem_of_nodup_bounded_length PC ncols hnd hpcb
          (by omega) c hc)
      · intro j hj
        rw [Finset.mem_range] at hj ⊢
        exact hpcb _ (getD_mem_lt PC j 0 hj)
      · intro c hc
        rw [Finset.mem_range] at hc
        have hmem := mem_of_nodup_bounded_length PC ncols hnd hpcb (by omega) c hc
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem
          (List.idxOf_lt_length_of_mem hmem)]
        exact List.getElem_idxOf (List.idxOf_lt_length_of_mem hmem)
      · intro j hj
        rw [Finset.mem_range] at hj
        rw [getD_lt_gen PC j 0 hj]
        exact List.Nodup.idxOf_getElem hnd j hj
      · intro j hj
        rw [Finset.mem_range] at hj
        have hmem := mem_of_nodup_bounded_length PC ncols hnd hpcb (by omega) j hj
        have : PC.getD (PC.idxOf j) 0 = j := by
          rw [getD_lt_gen PC _ 0 (List.idxOf_lt_length_of_mem hmem)]
          exact List.getElem_idxOf (List.idxOf_lt_length_of_mem hmem)
        rw [this]
    rw [hbij, hPClen]
    -- now collapse via the identity submatrix.
    rw [Finset.sum_eq_single i]
    · rw [hidval i i (by rw [hRPClen]; omega) (by omega), if_pos rfl, one_mul]
      -- v[PC[i]] = x[PC[i]] = R[i][ncols].
      have hPCi : PC.getD i 0 < ncols := hpcb _ (getD_mem_lt PC i 0 (by rw [hPClen]; omega))
      rw [getD_append_left _ _ _ _ (by rw [hxlen]; exact hPCi)]
      rw [show x = (List.range ncols).map (fun j =>
        match PC.idxOf? j with | some pr => (R.getD pr []).getD ncols 0 | none => 0) from rfl]
      rw [getD_lt_gen _ _ 0 (by rw [List.length_map, List.length_range]; exact hPCi)]
      rw [List.getElem_map, List.getElem_range]
      rw [idxOf?_of_mem PC (PC.getD i 0) (getD_mem_lt PC i 0 (by rw [hPClen]; omega))]
      rw [getD_lt_gen PC i 0 (by rw [hPClen]; omega)]
      rw [List.Nodup.idxOf_getElem hnd i (by rw [hPClen]; omega)]
    · intro j hj hji
      rw [hidval i j (by rw [hRPClen]; omega)
        (by rw [Finset.mem_range] at hj; omega), if_neg (Ne.symm hji), zero_mul]
    · intro hi'
      exfalso; apply hi'; rw [Finset.mem_range]; rw [hRPClen] at hi; omega
  rw [hmain]; ring

/-- The zero-free-variable back-read of a consistent RREF solves every RREF row. -/
theorem back_read_solves_rref_any (R : List (List ℚ)) (PC : List ℕ) (ncols : ℕ)
    (hid : isIdentitySubmatrix R PC) (hnd : PC.Nodup) (hpcb : ∀ c ∈ PC, c < ncols)
    (hrlen : ∀ r ∈ R, ncols + 1 ≤ r.length) :
    let x : List ℚ := (List.range ncols).map (fun j =>
      match PC.idxOf? j with | some pr => (R.getD pr []).getD ncols 0 | none => 0)
    solvesAll R (x ++ [(-1 : ℚ)]) := by
  obtain ⟨hRPClen, hidval⟩ := hid
  intro x r hr
  obtain ⟨i, hi, hri⟩ := List.getElem_of_mem hr
  rw [show r = R.getD i [] by rw [getD_lt_gen R i [] hi, hri]]
  have hiPC : i < PC.length := by rw [← hRPClen]; exact hi
  have hPCimem : PC.getD i 0 ∈ PC := getD_mem_lt PC i 0 hiPC
  have hPCi : PC.getD i 0 < ncols := hpcb _ hPCimem
  have hRlen_i : ncols + 1 ≤ (R.getD i []).length := hrlen _ (getD_mem_lt R i [] hi)
  have hxlen : x.length = ncols := by simp [x]
  have hvlen : (x ++ [(-1 : ℚ)]).length = ncols + 1 := by simp [hxlen]
  unfold solvesRow
  rw [dotQ_eq_sum (R.getD i []) (x ++ [(-1 : ℚ)]) (by rw [hvlen]; omega)]
  rw [hvlen, Finset.sum_range_succ]
  have hvncols : (x ++ [(-1 : ℚ)]).getD ncols 0 = -1 := by
    rw [getD_append_right _ _ _ _ (by rw [hxlen]), hxlen]
    simp
  rw [hvncols]
  have hmain :
      (∑ c ∈ Finset.range ncols,
          (R.getD i []).getD c 0 * (x ++ [(-1 : ℚ)]).getD c 0) =
        (R.getD i []).getD ncols 0 := by
    rw [Finset.sum_eq_single (PC.getD i 0)]
    · rw [hidval i i hi hiPC, if_pos rfl, one_mul]
      rw [getD_append_left x [(-1 : ℚ)] 0 (PC.getD i 0) (by rw [hxlen]; exact hPCi)]
      rw [show x = (List.range ncols).map (fun j =>
        match PC.idxOf? j with | some pr => (R.getD pr []).getD ncols 0 | none => 0) from rfl]
      rw [getD_lt_gen _ _ 0 (by rw [List.length_map, List.length_range]; exact hPCi)]
      rw [List.getElem_map, List.getElem_range]
      rw [idxOf?_of_mem PC (PC.getD i 0) hPCimem]
      rw [getD_lt_gen PC i 0 hiPC]
      rw [List.Nodup.idxOf_getElem hnd i hiPC]
    · intro c hc hci
      rw [Finset.mem_range] at hc
      by_cases hcmem : c ∈ PC
      · let j := PC.idxOf c
        have hj : j < PC.length := List.idxOf_lt_length_of_mem hcmem
        have hPCj : PC.getD j 0 = c := by
          rw [getD_lt_gen PC j 0 hj]
          exact List.getElem_idxOf hj
        have hij : i ≠ j := by
          intro hij
          apply hci
          rw [← hPCj, hij]
        rw [← hPCj, hidval i j hi hj, if_neg hij, zero_mul]
      · have hidx : PC.idxOf? c = none := by
          rw [List.idxOf?, List.findIdx?_eq_none_iff]
          intro a ha
          simp only [beq_eq_false_iff_ne]
          intro hac
          apply hcmem
          simpa [hac] using ha
        have hxget : (x ++ [(-1 : ℚ)]).getD c 0 = x.getD c 0 :=
          getD_append_left x [(-1 : ℚ)] 0 c (by rw [hxlen]; exact hc)
        have hxzero : x.getD c 0 = 0 := by
          simp [x, List.getD_eq_getElem?_getD, hc, hidx]
        rw [hxget, hxzero, mul_zero]
    · intro hnot
      exfalso
      apply hnot
      rw [Finset.mem_range]
      exact hPCi
  rw [hmain]
  ring

/-- The free-column vector of an RREF pivot system solves every homogeneous row. -/
private theorem freeColumn_solves_rref (R : List (List ℚ)) (PC : List ℕ) (ncols fc : ℕ)
    (hid : isIdentitySubmatrix R PC) (hnd : PC.Nodup) (hpcb : ∀ c ∈ PC, c < ncols)
    (hrlen : ∀ r ∈ R, ncols ≤ r.length) (hfc : fc < ncols) (hfree : fc ∉ PC) :
    let x : List ℚ := (List.range ncols).map (fun j =>
      if j = fc then 1
      else match PC.idxOf? j with
        | some pr => -((R.getD pr []).getD fc 0)
        | none => 0)
    solvesAll R x := by
  obtain ⟨hRPClen, hidval⟩ := hid
  intro x r hr
  obtain ⟨i, hi, hri⟩ := List.getElem_of_mem hr
  rw [show r = R.getD i [] by rw [getD_lt_gen R i [] hi, hri]]
  have hiPC : i < PC.length := by rw [← hRPClen]; exact hi
  have hRlen : ncols ≤ (R.getD i []).length := hrlen _ (getD_mem_lt R i [] hi)
  have hxlen : x.length = ncols := by simp [x]
  have hx_fc : x.getD fc 0 = 1 := by
    rw [show x = (List.range ncols).map (fun j =>
      if j = fc then 1 else match PC.idxOf? j with
        | some pr => -((R.getD pr []).getD fc 0)
        | none => 0) from rfl]
    rw [getD_lt_gen _ fc 0 (by rw [List.length_map, List.length_range]; exact hfc),
      List.getElem_map, List.getElem_range, if_pos rfl]
  have hx_pivot : ∀ j, j < PC.length →
      x.getD (PC.getD j 0) 0 = -((R.getD j []).getD fc 0) := by
    intro j hj
    have hpc : PC.getD j 0 < ncols := hpcb _ (getD_mem_lt PC j 0 hj)
    have hpc_ne : PC.getD j 0 ≠ fc := fun h =>
      hfree (h ▸ getD_mem_lt PC j 0 hj)
    rw [show x = (List.range ncols).map (fun k =>
      if k = fc then 1 else match PC.idxOf? k with
        | some pr => -((R.getD pr []).getD fc 0)
        | none => 0) from rfl]
    rw [getD_lt_gen _ _ 0 (by rw [List.length_map, List.length_range]; exact hpc),
      List.getElem_map, List.getElem_range, if_neg hpc_ne,
      idxOf?_of_mem PC (PC.getD j 0) (getD_mem_lt PC j 0 hj),
      getD_lt_gen PC j 0 hj, List.Nodup.idxOf_getElem hnd j hj]
  unfold solvesRow
  rw [dotQ_eq_sum (R.getD i []) x (by rw [hxlen]; exact hRlen)]
  let f : ℕ → ℚ := fun c => (R.getD i []).getD c 0 * x.getD c 0
  rw [hxlen]
  change (∑ c ∈ Finset.range ncols, f c) = 0
  have hsub : PC.toFinset ∪ {fc} ⊆ Finset.range ncols := by
    intro c hc
    rw [Finset.mem_union, Finset.mem_singleton] at hc
    rw [Finset.mem_range]
    rcases hc with hc | rfl
    · exact hpcb c (by simpa using hc)
    · exact hfc
  have hzero : ∀ c ∈ Finset.range ncols, c ∉ PC.toFinset ∪ {fc} → f c = 0 := by
    intro c hc hnot
    rw [Finset.mem_union, Finset.mem_singleton] at hnot
    have hpcFin : c ∉ PC.toFinset := fun h => hnot (Or.inl h)
    have hne : c ≠ fc := fun h => hnot (Or.inr h)
    have hpc : c ∉ PC := fun h => hpcFin (by simpa using h)
    have hc' : c < ncols := Finset.mem_range.mp hc
    have hidx : PC.idxOf? c = none := by
      rw [List.idxOf?, List.findIdx?_eq_none_iff]
      intro a ha
      simp only [beq_eq_false_iff_ne]
      intro hac
      exact hpc (by simpa [hac] using ha)
    have hxzero : x.getD c 0 = 0 := by
      rw [show x = (List.range ncols).map (fun k =>
        if k = fc then 1 else match PC.idxOf? k with
          | some pr => -((R.getD pr []).getD fc 0)
          | none => 0) from rfl]
      rw [getD_lt_gen _ c 0 (by rw [List.length_map, List.length_range]; exact hc'),
        List.getElem_map, List.getElem_range, if_neg hne, hidx]
    simp only [f, hxzero, mul_zero]
  have hext : (∑ c ∈ PC.toFinset ∪ {fc}, f c) = ∑ c ∈ Finset.range ncols, f c :=
    Finset.sum_subset hsub hzero
  have hbij : (∑ c ∈ PC.toFinset, f c) =
      ∑ j ∈ Finset.range PC.length, f (PC.getD j 0) := by
    apply Finset.sum_nbij' (fun c => PC.idxOf c) (fun j => PC.getD j 0)
    · intro c hc
      rw [Finset.mem_range]
      exact List.idxOf_lt_length_of_mem (by simpa using hc)
    · intro j hj
      rw [Finset.mem_range] at hj
      exact (by simpa using getD_mem_lt PC j 0 hj)
    · intro c hc
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem
        (List.idxOf_lt_length_of_mem (by simpa using hc))]
      exact List.getElem_idxOf (List.idxOf_lt_length_of_mem (by simpa using hc))
    · intro j hj
      rw [Finset.mem_range] at hj
      rw [getD_lt_gen PC j 0 hj]
      exact List.Nodup.idxOf_getElem hnd j hj
    · intro c hc
      have hcMem : c ∈ PC := by simpa using hc
      have hidx : PC.getD (PC.idxOf c) 0 = c := by
        rw [getD_lt_gen PC (PC.idxOf c) 0 (List.idxOf_lt_length_of_mem hcMem)]
        exact List.getElem_idxOf (List.idxOf_lt_length_of_mem hcMem)
      rw [hidx]
  have hpivsum : (∑ c ∈ PC.toFinset, f c) = -((R.getD i []).getD fc 0) := by
    rw [hbij, Finset.sum_eq_single i]
    · simp only [f]
      rw [hidval i i hi hiPC, if_pos rfl, one_mul, hx_pivot i hiPC]
    · intro j hj hji
      rw [Finset.mem_range] at hj
      simp only [f]
      rw [hidval i j hi hj, if_neg (Ne.symm hji), zero_mul]
    · intro hnot
      exact (hnot (Finset.mem_range.mpr hiPC)).elim
  have hdisj : Disjoint PC.toFinset {fc} :=
    Finset.disjoint_singleton_right.mpr (by simpa using hfree)
  rw [← hext, Finset.sum_union hdisj, hpivsum, Finset.sum_singleton]
  dsimp [f]
  rw [hx_fc]
  ring

/-- Output rows of `crref.go` are at least `ncols` wide. -/
theorem crref_go_rowlen (ncols : ℕ) :
    ∀ (fuel col : ℕ) (rest pivRows : List (List ℚ)) (pivCols : List ℕ),
      (∀ r ∈ rest ++ pivRows, ncols ≤ r.length) →
      ∀ r ∈ (crref.go ncols fuel col rest pivRows pivCols).1, ncols ≤ r.length := by
  intro fuel
  induction fuel with
  | zero =>
    intro col rest pivRows pivCols hrl r hr
    rw [crref.go] at hr
    exact hrl r (List.mem_append_right _ (by simpa using hr))
  | succ f ih =>
    intro col rest pivRows pivCols hrl r hr
    cases rest with
    | nil =>
      rw [crref.go] at hr
      · exact hrl r (List.mem_append_right _ (by simpa using hr))
      · nofun
    | cons r0 rs =>
      rw [crref.go] at hr
      rotate_left
      · nofun
      by_cases hcol : col ≥ ncols
      · rw [if_pos hcol] at hr
        exact hrl r (List.mem_append_right _ (by simpa using hr))
      · rw [if_neg hcol] at hr
        rw [not_le] at hcol
        cases hfind : (r0 :: rs).find? (fun r => decide ((r.getD col 0) ≠ 0)) with
        | none =>
          rw [hfind] at hr
          exact ih (col + 1) (r0 :: rs) pivRows pivCols hrl r hr
        | some pr =>
          rw [hfind] at hr
          have hprmem : pr ∈ (r0 :: rs) := List.mem_of_find?_eq_some hfind
          have hprlen : ncols ≤ pr.length := hrl pr (List.mem_append_left _ hprmem)
          set piv : ℚ := pr.getD col 0
          set prn : List ℚ := pr.map (· / piv) with hprndef
          set elim : List ℚ → List ℚ :=
            (fun r => List.zipWith (fun ri pi => ri - (r.getD col 0) * pi) r prn) with helimdef
          have helim_len : ∀ s, ncols ≤ s.length → ncols ≤ (elim s).length := by
            intro s hs; rw [helimdef]; simp only [List.length_zipWith]
            rw [hprndef, List.length_map]; omega
          refine ih (col + 1) _ (prn :: pivRows.map elim) (col :: pivCols) ?_ r hr
          intro s hs
          rw [List.mem_append] at hs
          rcases hs with hs | hs
          · rw [List.mem_map] at hs
            obtain ⟨t, ht, rfl⟩ := hs
            rw [List.mem_filter] at ht
            exact helim_len t (hrl t (List.mem_append_left _ ht.1))
          · rcases List.mem_cons.mp hs with rfl | hs'
            · rw [hprndef, List.length_map]; exact hprlen
            · rw [List.mem_map] at hs'
              obtain ⟨t, ht, rfl⟩ := hs'
              exact helim_len t (hrl t (List.mem_append_right _ ht))

/-- Output rows of `crref` are at least `ncols` wide. -/
theorem crref_rowlen (rows : List (List ℚ)) (ncols : ℕ)
    (hrows : ∀ r ∈ rows, ncols ≤ r.length) :
    ∀ r ∈ (crref rows ncols).1, ncols ≤ r.length :=
  crref_go_rowlen ncols (ncols + rows.length + 1) 0 rows [] [] (by simpa using hrows)

/-- A returned `cConstSolveUniqueQ` solution has length exactly `ncols`. -/
theorem cConstSolveUniqueQ_length (Arows : List (List ℚ)) (urhs : List ℚ) (ncols : ℕ)
    (x : List ℚ) (hsome : cConstSolveUniqueQ Arows urhs ncols = some x) :
    x.length = ncols := by
  rw [cConstSolveUniqueQ] at hsome
  set RPC := crref (List.zipWith (fun r u => r ++ [u]) Arows urhs) (ncols + 1)
  by_cases hc1 : RPC.2.contains ncols
  · simp only [hc1, if_true] at hsome; exact absurd hsome (by simp)
  · simp only [hc1, Bool.false_eq_true, if_false] at hsome
    by_cases hc2 : RPC.2.length < ncols
    · simp only [hc2, if_true] at hsome; exact absurd hsome (by simp)
    · simp only [hc2, if_false, Option.some.injEq] at hsome
      rw [← hsome, List.length_map, List.length_range]

/-- A returned particular rational solution has exactly `ncols` entries. -/
theorem cConstSolveAnyQ_length (Arows : List (List ℚ)) (urhs : List ℚ) (ncols : ℕ)
    (x : List ℚ) (hsome : cConstSolveAnyQ Arows urhs ncols = some x) :
    x.length = ncols := by
  rw [cConstSolveAnyQ] at hsome
  set RPC := crref (List.zipWith (fun r u => r ++ [u]) Arows urhs) (ncols + 1)
  by_cases hc : RPC.2.contains ncols
  · simp only [hc, if_true] at hsome
    exact absurd hsome (by simp)
  · simp only [hc, Bool.false_eq_true, if_false, Option.some.injEq] at hsome
    rw [← hsome, List.length_map, List.length_range]

/-- Every vector returned by `cNullspaceBasisQ` has exactly `ncols` entries. -/
theorem cNullspaceBasisQ_mem_length (rows : List (List ℚ)) (ncols : ℕ) (x : List ℚ)
    (hx : x ∈ cNullspaceBasisQ rows ncols) : x.length = ncols := by
  unfold cNullspaceBasisQ at hx
  rw [List.mem_map] at hx
  obtain ⟨fc, _, rfl⟩ := hx
  simp

/-- Every vector returned by `cNullspaceBasisQ` solves the original homogeneous system. -/
theorem cNullspaceBasisQ_mem_solves (rows : List (List ℚ)) (ncols : ℕ) (x : List ℚ)
    (hwidth : ∀ r ∈ rows, r.length = ncols)
    (hx : x ∈ cNullspaceBasisQ rows ncols) :
    ∀ i, i < rows.length → dotQ (rows.getD i []) x = 0 := by
  unfold cNullspaceBasisQ at hx
  split at hx
  next R PC hcrref =>
    rw [List.mem_map] at hx
    obtain ⟨fc, hfc, rfl⟩ := hx
    rw [List.mem_filter] at hfc
    have hfcLt : fc < ncols := List.mem_range.mp hfc.1
    have hfree : fc ∉ PC := by
      intro hmem
      simp [hmem] at hfc
    have hwidth' : ∀ r ∈ rows, ncols ≤ r.length := fun r hr => le_of_eq (hwidth r hr).symm
    obtain ⟨hid, hnd, hpcb⟩ := crref_rref rows ncols hwidth'
    rw [hcrref] at hid hnd hpcb
    have hrlen : ∀ r ∈ R, ncols ≤ r.length := by
      have h := crref_rowlen rows ncols hwidth'
      simpa [hcrref] using h
    have hsolR := freeColumn_solves_rref R PC ncols fc hid hnd hpcb hrlen hfcLt hfree
    have hsol : solvesAll rows ((List.range ncols).map (fun j =>
        if j = fc then 1 else match PC.idxOf? j with
          | some pr => -((R.getD pr []).getD fc 0)
          | none => 0)) :=
      crref_solves rows ncols _ (by simp) (by
        intro r hr
        rw [hwidth r hr]
        simp) (by
        rw [hcrref]
        exact hsolR)
    intro i hi
    exact hsol _ (getD_mem_lt rows i [] hi)

/-- Soundness of `cConstSolveUniqueQ`: if it returns `some x`, then `x` solves `A·x = b` rowwise,
`dotQ (Arows.getD i []) x = urhs.getD i 0` for each `i < Arows.length`. -/
theorem cConstSolveUniqueQ_sound (Arows : List (List ℚ)) (urhs : List ℚ) (ncols : ℕ) (x : List ℚ)
    (hwidth : ∀ r ∈ Arows, r.length = ncols) (hlen : Arows.length = urhs.length)
    (hsome : cConstSolveUniqueQ Arows urhs ncols = some x) :
    ∀ i, i < Arows.length → dotQ (Arows.getD i []) x = urhs.getD i 0 := by
  -- the augmented matrix and its RREF.
  set aug : List (List ℚ) := List.zipWith (fun r u => r ++ [u]) Arows urhs with haugdef
  set RPC := crref aug (ncols + 1) with hRPCdef
  -- augmented rows are exactly ncols+1 wide.
  have haug_len : aug.length = Arows.length := by rw [haugdef, List.length_zipWith]; omega
  have haug_width : ∀ r ∈ aug, r.length = ncols + 1 := by
    intro r hr
    rw [haugdef, List.mem_iff_getElem] at hr
    obtain ⟨k, hk, rfl⟩ := hr
    rw [List.length_zipWith] at hk
    rw [List.getElem_zipWith, List.length_append, List.length_singleton,
      hwidth _ (List.getElem_mem _)]
  have haug_width_ge : ∀ r ∈ aug, ncols + 1 ≤ r.length := fun r hr => le_of_eq (haug_width r hr).symm
  -- unfold cConstSolveUniqueQ.
  rw [cConstSolveUniqueQ] at hsome
  simp only [← haugdef, ← hRPCdef] at hsome
  -- split on the two `none` guards.
  by_cases hc1 : RPC.2.contains (ncols)
  · rw [if_pos hc1] at hsome; exact absurd hsome (by simp)
  · rw [if_neg hc1] at hsome
    by_cases hc2 : RPC.2.length < ncols
    · rw [if_pos hc2] at hsome; exact absurd hsome (by simp)
    · rw [if_neg hc2] at hsome
      rw [Option.some.injEq] at hsome
      -- structural facts from crref_rref.
      obtain ⟨hid, hnd, hpcb⟩ := crref_rref aug (ncols + 1) haug_width_ge
      have hrlen : ∀ r ∈ RPC.1, ncols + 1 ≤ r.length := crref_rowlen aug (ncols + 1) haug_width_ge
      -- pivot columns are all `< ncols` (not the rhs column `ncols`).
      have hncols_not_mem : ncols ∉ RPC.2 := by simpa using hc1
      have hpcb' : ∀ c ∈ RPC.2, c < ncols := by
        intro c hc
        have hlt : c < ncols + 1 := hpcb c hc
        rcases Nat.lt_succ_iff_lt_or_eq.mp hlt with h | h
        · exact h
        · exact absurd (h ▸ hc) hncols_not_mem
      -- full rank: PC.length ≥ ncols.
      have hrank : ncols ≤ RPC.2.length := by omega
      -- P1: the back-read solves the RREF rows.
      have hP1 := back_read_solves_rref RPC.1 RPC.2 ncols hid hnd hpcb' hrank hrlen
      -- the back-read vector is exactly `x ++ [-1]` (x = hsome).
      set xvec : List ℚ := (List.range ncols).map (fun j =>
        match RPC.2.idxOf? j with | some pr => (RPC.1.getD pr []).getD ncols 0 | none => 0) with hxvecdef
      have hxeq : x = xvec := hsome.symm
      -- crref_solves: solutions of RREF rows are solutions of aug rows.
      have hvlen : (xvec ++ [(-1 : ℚ)]).length = ncols + 1 := by
        rw [List.length_append, hxvecdef]; simp
      have hsolveAug : solvesAll aug (xvec ++ [(-1 : ℚ)]) := by
        apply crref_solves aug (ncols + 1) (xvec ++ [(-1 : ℚ)]) (by rw [hvlen])
          (fun r hr => by rw [hvlen]; exact haug_width_ge r hr)
        rw [← hRPCdef]
        exact hP1
      -- extract per-row A·x = b.
      intro i hi
      have haugi : aug.getD i [] = Arows.getD i [] ++ [urhs.getD i 0] := by
        rw [haugdef, getD_lt_gen _ i [] (by rw [List.length_zipWith]; omega), List.getElem_zipWith,
          getD_lt_gen Arows i [] hi, getD_lt_gen urhs i 0 (by omega)]
      have hsolvei : solvesRow (aug.getD i []) (xvec ++ [(-1 : ℚ)]) :=
        hsolveAug _ (getD_mem_lt aug i [] (by rw [haug_len]; exact hi))
      rw [haugi] at hsolvei
      rw [hxeq]
      -- compute the zipWith over the appended lists.
      have hcompute : dotQ (Arows.getD i [] ++ [urhs.getD i 0]) (xvec ++ [(-1 : ℚ)])
          = dotQ (Arows.getD i []) xvec - urhs.getD i 0 := by
        have hAlen : (Arows.getD i []).length = ncols := hwidth _ (getD_mem_lt Arows i [] hi)
        have hxveclen : xvec.length = ncols := by rw [hxvecdef]; simp
        unfold dotQ
        rw [List.zipWith_append (by rw [hAlen, hxveclen])]
        simp only [List.zipWith_cons_cons, List.zipWith_nil_left, List.sum_append, List.sum_cons,
          List.sum_nil, add_zero]
        ring
      unfold solvesRow at hsolvei
      rw [hcompute] at hsolvei
      linarith [hsolvei]

/-- Soundness of `cConstSolveAnyQ`: every returned vector solves the well-formed rational system. -/
theorem cConstSolveAnyQ_sound (Arows : List (List ℚ)) (urhs : List ℚ) (ncols : ℕ) (x : List ℚ)
    (hwidth : ∀ r ∈ Arows, r.length = ncols) (hlen : Arows.length = urhs.length)
    (hsome : cConstSolveAnyQ Arows urhs ncols = some x) :
    ∀ i, i < Arows.length → dotQ (Arows.getD i []) x = urhs.getD i 0 := by
  set aug : List (List ℚ) := List.zipWith (fun r u => r ++ [u]) Arows urhs with haugdef
  set RPC := crref aug (ncols + 1) with hRPCdef
  have haug_len : aug.length = Arows.length := by
    rw [haugdef, List.length_zipWith]
    omega
  have haug_width : ∀ r ∈ aug, r.length = ncols + 1 := by
    intro r hr
    rw [haugdef, List.mem_iff_getElem] at hr
    obtain ⟨k, hk, rfl⟩ := hr
    rw [List.length_zipWith] at hk
    rw [List.getElem_zipWith, List.length_append, List.length_singleton,
      hwidth _ (List.getElem_mem _)]
  have haug_width_ge : ∀ r ∈ aug, ncols + 1 ≤ r.length :=
    fun r hr => le_of_eq (haug_width r hr).symm
  rw [cConstSolveAnyQ] at hsome
  simp only [← haugdef, ← hRPCdef] at hsome
  by_cases hc : RPC.2.contains ncols
  · rw [if_pos hc] at hsome
    exact absurd hsome (by simp)
  · rw [if_neg hc, Option.some.injEq] at hsome
    obtain ⟨hid, hnd, hpcb⟩ := crref_rref aug (ncols + 1) haug_width_ge
    have hrlen : ∀ r ∈ RPC.1, ncols + 1 ≤ r.length :=
      crref_rowlen aug (ncols + 1) haug_width_ge
    have hncols_not_mem : ncols ∉ RPC.2 := by simpa using hc
    have hpcb' : ∀ c ∈ RPC.2, c < ncols := by
      intro c hcmem
      have hlt : c < ncols + 1 := hpcb c hcmem
      rcases Nat.lt_succ_iff_lt_or_eq.mp hlt with h | h
      · exact h
      · exact absurd (h ▸ hcmem) hncols_not_mem
    set xvec : List ℚ := (List.range ncols).map (fun j =>
      match RPC.2.idxOf? j with
      | some pr => (RPC.1.getD pr []).getD ncols 0
      | none => 0) with hxvecdef
    have hxeq : x = xvec := hsome.symm
    have hP1 := back_read_solves_rref_any RPC.1 RPC.2 ncols hid hnd hpcb' hrlen
    have hvlen : (xvec ++ [(-1 : ℚ)]).length = ncols + 1 := by
      rw [List.length_append, hxvecdef]
      simp
    have hsolveAug : solvesAll aug (xvec ++ [(-1 : ℚ)]) := by
      apply crref_solves aug (ncols + 1) (xvec ++ [(-1 : ℚ)]) (by rw [hvlen])
        (fun r hr => by rw [hvlen]; exact haug_width_ge r hr)
      rw [← hRPCdef]
      exact hP1
    intro i hi
    have haugi : aug.getD i [] = Arows.getD i [] ++ [urhs.getD i 0] := by
      rw [haugdef, getD_lt_gen _ i [] (by rw [List.length_zipWith]; omega),
        List.getElem_zipWith, getD_lt_gen Arows i [] hi,
        getD_lt_gen urhs i 0 (by omega)]
    have hsolvei : solvesRow (aug.getD i []) (xvec ++ [(-1 : ℚ)]) :=
      hsolveAug _ (getD_mem_lt aug i [] (by rw [haug_len]; exact hi))
    rw [haugi] at hsolvei
    rw [hxeq]
    have hcompute : dotQ (Arows.getD i [] ++ [urhs.getD i 0]) (xvec ++ [(-1 : ℚ)])
        = dotQ (Arows.getD i []) xvec - urhs.getD i 0 := by
      have hAlen : (Arows.getD i []).length = ncols :=
        hwidth _ (getD_mem_lt Arows i [] hi)
      have hxveclen : xvec.length = ncols := by rw [hxvecdef]; simp
      unfold dotQ
      rw [List.zipWith_append (by rw [hAlen, hxveclen])]
      simp only [List.zipWith_cons_cons, List.zipWith_nil_left, List.sum_append,
        List.sum_cons, List.sum_nil, add_zero]
      ring
    unfold solvesRow at hsolvei
    rw [hcompute] at hsolvei
    linarith [hsolvei]


end DeepWiki.SymbolicIntegration.DensePoly

namespace DeepWiki.SymbolicIntegration

/-- The abstract coefficient-list dot product agrees with the rational solver's `dotQ`. -/
theorem linearDot_rat_eq_dotQ (row x : List ℚ) :
    linearDot row x = DensePoly.dotQ row x := by
  unfold linearDot DensePoly.dotQ
  induction row generalizing x with
  | nil => rfl
  | cons a row ih =>
    cases x with
    | nil => rfl
    | cons b x =>
      change a * b + (List.zipWith (fun x1 x2 => x1 * x2) row x).sum = _
      simp [List.zipWith_cons_cons, List.sum_cons]

/-- The rational RREF solver satisfies the abstract lawful linear-solver interface. -/
instance instLawfulCLinearSolveRat : LawfulCLinearSolve ℚ where
  solveUnique_length := by
    intro rows rhs ncols x hsome
    exact DensePoly.cConstSolveUniqueQ_length rows rhs ncols x hsome
  solveUnique_sound := by
    intro rows rhs ncols x hwidth hlen hsome i hi
    change linearDot (rows.getD i []) x = rhs.getD i CCommRing.zero
    rw [linearDot_rat_eq_dotQ]
    exact DensePoly.cConstSolveUniqueQ_sound rows rhs ncols x hwidth hlen hsome i hi
  solveAny_length := by
    intro rows rhs ncols x hsome
    exact DensePoly.cConstSolveAnyQ_length rows rhs ncols x hsome
  solveAny_sound := by
    intro rows rhs ncols x hwidth hlen hsome i hi
    change linearDot (rows.getD i []) x = rhs.getD i CCommRing.zero
    rw [linearDot_rat_eq_dotQ]
    exact DensePoly.cConstSolveAnyQ_sound rows rhs ncols x hwidth hlen hsome i hi
  nullspaceBasis_length := by
    intro rows ncols x hx
    exact DensePoly.cNullspaceBasisQ_mem_length rows ncols x hx
  nullspaceBasis_sound := by
    intro rows ncols x hwidth hx i hi
    rw [linearDot_rat_eq_dotQ]
    exact DensePoly.cNullspaceBasisQ_mem_solves rows ncols x hwidth hx i hi

end DeepWiki.SymbolicIntegration
