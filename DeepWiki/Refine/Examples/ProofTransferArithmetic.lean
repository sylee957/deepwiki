import DeepWiki.Refine.Examples.BinaryNaturals
import DeepWiki.Refine.IntegerModularRetraction

/-! # Arithmetic examples of proof transfer

Ground computations and quantified arithmetic statements can be transported through equivalent
or retractive number representations. -/

namespace DeepWiki.Refine

/-- The three-factor benchmark sequence in unary natural numbers. -/
def multiplicationBenchmark : List Nat :=
  [100, 101, 102]

/-- The three-factor benchmark sequence in canonical binary natural numbers. -/
def binaryMultiplicationBenchmark : List BinaryNat :=
  multiplicationBenchmark.map BinaryNat.ofNat

/-- The binary benchmark comparison computes to true. -/
theorem binaryMultiplicationBenchmark_ltb_eq_true :
    BinaryNat.ltb (BinaryNat.listProduct binaryMultiplicationBenchmark)
      (BinaryNat.listProduct
        (binaryMultiplicationBenchmark ++ binaryMultiplicationBenchmark)) = true := by
  rfl

/-- The binary benchmark satisfies the transported product comparison. -/
theorem binaryMultiplicationBenchmark_prod_lt_append_prod :
    (BinaryNat.listProduct binaryMultiplicationBenchmark).toNat <
      (BinaryNat.listProduct
        (binaryMultiplicationBenchmark ++ binaryMultiplicationBenchmark)).toNat :=
  (BinaryNat.ltb_eq_true_iff _ _).mp binaryMultiplicationBenchmark_ltb_eq_true

/-- The unary benchmark comparison follows by transport from binary computation. -/
theorem multiplicationBenchmark_prod_lt_append_prod :
    multiplicationBenchmark.prod < (multiplicationBenchmark ++ multiplicationBenchmark).prod := by
  simpa [binaryMultiplicationBenchmark, Function.comp_def] using
    binaryMultiplicationBenchmark_prod_lt_append_prod

/-- The concrete integer product vanishes after reduction modulo nine. -/
theorem groundProduct_eq_zero_mod_nine :
    ((23649 : ZMod 9) * (23703 : ZMod 9)) = 0 := by
  native_decide

/-- The concrete integer product is divisible by nine. -/
theorem nine_dvd_groundProduct : (9 : ℤ) ∣ 23649 * 23703 := by
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd (23649 * 23703) 9).mp
  native_decide

/-- Units modulo nine cannot solve the cubic equation `x³ + y³ = z³`. -/
theorem zmodNine_cubic_ne_of_mul_isUnit :
    ∀ x y z : ZMod 9, IsUnit (x * y * z) → x ^ 3 + y ^ 3 ≠ z ^ 3 := by
  native_decide

/-- If three does not divide `x * y * z`, then `x³ + y³ ≠ z³`. -/
theorem nat_cubic_ne_of_three_not_dvd_mul (x y z : Nat)
    (hnot : ¬ 3 ∣ x * y * z) : x ^ 3 + y ^ 3 ≠ z ^ 3 := by
  have hcoprimeThree : (x * y * z).Coprime 3 :=
    (Nat.prime_three.coprime_iff_not_dvd.mpr hnot).symm
  have hcoprimeNine : (x * y * z).Coprime 9 := by
    simpa only [show 9 = 3 ^ 2 by decide] using hcoprimeThree.pow_right 2
  have hunit : IsUnit ((x * y * z : Nat) : ZMod 9) :=
    (ZMod.isUnit_iff_coprime (x * y * z) 9).mpr hcoprimeNine
  have hunit' : IsUnit ((x : ZMod 9) * (y : ZMod 9) * (z : ZMod 9)) := by
    simpa only [Nat.cast_mul] using hunit
  intro heq
  apply zmodNine_cubic_ne_of_mul_isUnit (x : ZMod 9) (y : ZMod 9) (z : ZMod 9) hunit'
  simpa only [Nat.cast_add, Nat.cast_pow] using
    congrArg (fun value : Nat ↦ (value : ZMod 9)) heq

example :
    multiplicationBenchmark.prod < (multiplicationBenchmark ++ multiplicationBenchmark).prod :=
  multiplicationBenchmark_prod_lt_append_prod

example :
    (BinaryNat.listProduct binaryMultiplicationBenchmark).toNat <
      (BinaryNat.listProduct
        (binaryMultiplicationBenchmark ++ binaryMultiplicationBenchmark)).toNat :=
  binaryMultiplicationBenchmark_prod_lt_append_prod

example :
    BinaryNat.ltb (BinaryNat.listProduct binaryMultiplicationBenchmark)
      (BinaryNat.listProduct
        (binaryMultiplicationBenchmark ++ binaryMultiplicationBenchmark)) = true :=
  binaryMultiplicationBenchmark_ltb_eq_true

example : ((23649 : ZMod 9) * (23703 : ZMod 9)) = 0 :=
  groundProduct_eq_zero_mod_nine

example : (9 : ℤ) ∣ 23649 * 23703 :=
  nine_dvd_groundProduct

example (x y z : Nat) (hnot : ¬ 3 ∣ x * y * z) : x ^ 3 + y ^ 3 ≠ z ^ 3 :=
  nat_cubic_ne_of_three_not_dvd_mul x y z hnot

end DeepWiki.Refine
