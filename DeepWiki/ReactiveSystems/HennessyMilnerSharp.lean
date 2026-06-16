import DeepWiki.ReactiveSystems.HennessyMilner

/-! # Sharpness of the Hennessy–Milner theorem (Exercise 5.13)
The Hennessy–Milner theorem (`hennessyMilner`) assumes image-finiteness. This is
necessary: over the image-infinite LTS below — where `lt` (the process `A<ω`)
can step to a chain of every finite length, and `top` (`Aω + A<ω`) can in
addition step to the infinite chain `omega` — the states `lt` and `top` satisfy
exactly the same HML formulae yet are not strongly bisimilar. The HML-equivalence
follows because every formula has finite modal depth and so cannot see the
difference; non-bisimilarity because `top`'s infinite branch cannot be matched by
any finite chain of `lt`. -/

namespace DeepWiki.ReactiveSystems

open LTS

inductive HMState | chain : ℕ → HMState | omega : HMState | lt : HMState | top : HMState
  deriving DecidableEq

def hmStep : HMState → Unit → HMState → Prop
  | .chain (n+1), _, .chain m => m = n
  | .omega, _, .omega => True
  | .lt, _, .chain _ => True
  | .top, _, .omega => True
  | .top, _, .chain _ => True
  | _, _, _ => False

def hmLTS : LTS HMState Unit := ⟨hmStep⟩

/-- Modal depth of an HML formula: the maximal nesting of modalities `⟨a⟩`/`[a]`. -/
def modalDepth : HML Unit → ℕ
  | .tt => 0
  | .ff => 0
  | .and F G => max (modalDepth F) (modalDepth G)
  | .or F G => max (modalDepth F) (modalDepth G)
  | .dia _ F => modalDepth F + 1
  | .box _ F => modalDepth F + 1

/-- `omega` and `chain m` agree on every formula of modal depth `≤ m`. -/
theorem omega_sat_iff_chain (F : HML Unit) {m : ℕ} (hm : modalDepth F ≤ m) :
    (HMState.omega ⊨[hmLTS] F) ↔ (HMState.chain m ⊨[hmLTS] F) := by
  induction F generalizing m with
  | tt => simp
  | ff => simp
  | and F G ihF ihG =>
    simp only [modalDepth, max_le_iff] at hm
    simp only [sat_and, ihF hm.1, ihG hm.2]
  | or F G ihF ihG =>
    simp only [modalDepth, max_le_iff] at hm
    simp only [sat_or, ihF hm.1, ihG hm.2]
  | dia a F ih =>
    simp only [modalDepth] at hm
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    have hsub : modalDepth F ≤ k := by omega
    simp only [sat_dia]
    constructor
    · rintro ⟨q, hq, hsat⟩
      cases q with
      | omega => exact ⟨HMState.chain k, by simp [hmLTS, hmStep], (ih hsub).mp hsat⟩
      | _ => simp [hmLTS, hmStep] at hq
    · rintro ⟨q, hq, hsat⟩
      cases q with
      | chain j =>
        simp only [hmLTS, hmStep] at hq
        subst hq
        exact ⟨HMState.omega, by simp [hmLTS, hmStep], (ih hsub).mpr hsat⟩
      | _ => simp [hmLTS, hmStep] at hq
  | box a F ih =>
    simp only [modalDepth] at hm
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    have hsub : modalDepth F ≤ k := by omega
    simp only [sat_box]
    constructor
    · intro h q hq
      cases q with
      | chain j =>
        simp only [hmLTS, hmStep] at hq
        subst hq
        exact (ih hsub).mp (h HMState.omega (by simp [hmLTS, hmStep]))
      | _ => simp [hmLTS, hmStep] at hq
    · intro h q hq
      cases q with
      | omega =>
        exact (ih hsub).mpr (h (HMState.chain k) (by simp [hmLTS, hmStep]))
      | _ => simp [hmLTS, hmStep] at hq

/-- `lt` and `top` are Hennessy–Milner equivalent (the image-infinite counterexample). -/
theorem lt_hmlEquiv_top : hmLTS.HMLEquiv HMState.lt HMState.top := by
  intro F
  induction F with
  | tt => simp
  | ff => simp
  | and F G ihF ihG => simp only [sat_and, ihF, ihG]
  | or F G ihF ihG => simp only [sat_or, ihF, ihG]
  | dia a F _ =>
    simp only [sat_dia]
    constructor
    · rintro ⟨q, hq, hsat⟩
      cases q with
      | chain j => exact ⟨HMState.chain j, by simp [hmLTS, hmStep], hsat⟩
      | _ => simp [hmLTS, hmStep] at hq
    · rintro ⟨q, hq, hsat⟩
      cases q with
      | omega =>
        exact ⟨HMState.chain (modalDepth F), by simp [hmLTS, hmStep],
          (omega_sat_iff_chain F (le_refl _)).mp hsat⟩
      | chain j => exact ⟨HMState.chain j, by simp [hmLTS, hmStep], hsat⟩
      | _ => simp [hmLTS, hmStep] at hq
  | box a F _ =>
    simp only [sat_box]
    constructor
    · intro h q hq
      cases q with
      | omega =>
        exact (omega_sat_iff_chain F (le_refl _)).mpr (h (HMState.chain (modalDepth F))
          (by simp [hmLTS, hmStep]))
      | chain j =>
        exact h (HMState.chain j) (by simp [hmLTS, hmStep])
      | _ => simp [hmLTS, hmStep] at hq
    · intro h q hq
      cases q with
      | chain j =>
        exact h (HMState.chain j) (by simp [hmLTS, hmStep])
      | _ => simp [hmLTS, hmStep] at hq

/-- `chain k` is never bisimilar to `omega`: `chain` halts after `k` steps, `omega` never does. -/
theorem chain_not_bisimilar_omega (k : ℕ) : ¬ (HMState.chain k ~[hmLTS] HMState.omega) := by
  induction k with
  | zero =>
    intro h
    obtain ⟨q, hq, _⟩ := ((bisimilar_iff _ _).mp h).2 () HMState.omega (by simp [hmLTS, hmStep])
    simp [hmLTS, hmStep] at hq
  | succ k ih =>
    intro h
    obtain ⟨q, hq, hb⟩ := ((bisimilar_iff _ _).mp h).1 () (HMState.chain k)
      (by simp [hmLTS, hmStep])
    simp only [hmLTS, hmStep] at hq
    cases q with
    | omega => exact ih hb
    | _ => simp at hq

/-- `lt` is not bisimilar to `top`: matching `top --a--> omega` forces a `chain ~ omega`. -/
theorem lt_not_bisimilar_top : ¬ (HMState.lt ~[hmLTS] HMState.top) := by
  intro h
  obtain ⟨q, hq, hb⟩ := ((bisimilar_iff _ _).mp h).2 () HMState.omega (by simp [hmLTS, hmStep])
  simp only [hmLTS, hmStep] at hq
  cases q with
  | chain j => exact chain_not_bisimilar_omega j hb
  | _ => simp at hq

/-- `hmLTS` is not image-finite: `lt` has infinitely many successors (all of `chain`). -/
theorem hmLTS_not_imageFinite : ¬ hmLTS.ImageFinite := by
  intro h
  have hfin := h HMState.lt ()
  have hsub : Set.range HMState.chain ⊆ {p' | hmLTS.step HMState.lt () p'} := by
    rintro _ ⟨n, rfl⟩
    simp [hmLTS, hmStep]
  have hinf : (Set.range HMState.chain).Infinite :=
    Set.infinite_range_of_injective (fun a b hab => by injection hab)
  exact hinf (hfin.subset hsub)

/-- Exercise 5.13: the Hennessy–Milner theorem fails without image-finiteness. -/
theorem hennessyMilner_needs_imageFinite :
    ∃ (P : Type) (L : LTS P Unit) (p q : P),
      ¬ L.ImageFinite ∧ L.HMLEquiv p q ∧ ¬ (p ~[L] q) :=
  ⟨HMState, hmLTS, HMState.lt, HMState.top, hmLTS_not_imageFinite, lt_hmlEquiv_top,
    lt_not_bisimilar_top⟩

end DeepWiki.ReactiveSystems
