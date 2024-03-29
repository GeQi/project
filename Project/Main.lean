import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.GroupTheory.Exponent
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.GroupPower.Basic
import Mathlib.Algebra.Group.Commute.Defs
import Mathlib.FieldTheory.AbsoluteGaloisGroup
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.RingTheory.RootsOfUnity.Basic

/-!
Lemmas and where to put them?
-/

/-!
The exponent of a group divides the integral annihilating powers
-/
@[to_additive (attr := simp)]
theorem Group.exponent_dvd_of_forall_pow_eq_one (G : Type*) [Group G] (n : ℤ)
      (hG : ∀ (g : G), g ^ n = 1) :
    ((Monoid.exponent G) : ℤ) ∣ n := by
  match n with
  | Int.ofNat m =>
    have h : ∀ g : G, g ^ m = 1 := by
      intro g
      rw [← zpow_natCast]
      exact hG g
    have hh : Monoid.exponent G ∣ m := by
      exact Monoid.exponent_dvd_of_forall_pow_eq_one h
    exact Int.ofNat_dvd_left.mpr hh
  | Int.negSucc m =>
    have h : ∀ g : G, g ^ (-(m+1 : ℤ)) = 1 := hG
    have hh : ∀ g : G, g ^ (m+1) = 1 := by
      intro g
      calc
        g ^ (m+1) = (g ^ (-(m+1 : ℤ)))⁻¹ := by group
        _ = 1 := by rw [h g, inv_one]
    have hhh : Monoid.exponent G ∣ (m+1) := by
      exact Monoid.exponent_dvd_of_forall_pow_eq_one hh
    have hhhh : ((Monoid.exponent G) : ℤ) ∣ (m+1) := by
      exact Int.ofNat_dvd_left.mpr hhh
    exact Int.dvd_neg.mp hhhh

/-!
d ∈ (-n, n) and n ∣ d implies d = 0
-/
lemma zero_of_bounded_divisor {d n : ℤ} (h1 : -n < d) (h2 : d < n) (h3 : n ∣ d): d = 0 := by
  obtain ⟨c, hc⟩ := h3
  rw [hc] at h1 h2
  have : c = 0 := by nlinarith
  rw [this] at hc
  simp only [mul_zero] at hc
  exact hc

/-!
if n ∣ a - b and 0 ≤ a, b < n, then a = b
-/
lemma zmod_val_sub_div_by_n_eq (n : ℕ) [nz: NeZero n] (a b : ZMod n) (h : (n : ℤ) ∣ (ZMod.val a - ZMod.val b)) :
    a = b := by
  have h1 : ZMod.val a < n := by apply ZMod.val_lt
  have h2 : ZMod.val b < n := by apply ZMod.val_lt
  have h3 : -(n : ℤ) < ZMod.val a - ZMod.val b := by
    linarith
  have h4 : ZMod.val a - ZMod.val b < (n : ℤ) := by
    linarith
  have h5 : (ZMod.val a : ℤ) - ZMod.val b = 0 := by
    exact zero_of_bounded_divisor h3 h4 h
  have h6 : ZMod.val a = ZMod.val b := by
    linarith
  cases n
  · simp only [Nat.zero_eq, neZero_zero_iff_false] at nz
  · simp only [ZMod.val, ZMod.val_nat_cast] at h6
    exact Fin.eq_of_val_eq h6

@[to_additive]
lemma pow_eq_one_of_order_dvd {G : Type*} [Group G] (g: G) (a: ℤ)
    (hh : (Monoid.exponent G : ℤ) ∣ a) : g ^ a = 1 := by
  obtain ⟨c, hc⟩ := hh
  rw [hc, zpow_mul, zpow_natCast, Monoid.pow_exponent_eq_one, one_zpow]

@[to_additive]
lemma pow_eq_pow_of_order_dvd_dif {G : Type*} [Group G] (g: G) (a b: ℤ)
    (h : (Monoid.exponent G : ℤ) ∣ a - b) : g ^ a = g ^ b := by
  rw [← mul_inv_eq_one, ← zpow_sub]
  exact pow_eq_one_of_order_dvd g (a - b) h

@[simp]
lemma zmod_val_mul_mod (n : ℕ) (a b : ZMod n) :
    (n : ℤ) ∣ ((ZMod.val a : ℤ) * (ZMod.val b : ℤ) - (ZMod.val (a * b) : ℤ)) := by
  rw [Int.dvd_iff_emod_eq_zero, ZMod.val_mul]
  simp only [Int.ofNat_emod, Nat.cast_mul, EuclideanDomain.mod_eq_zero]
  exact Int.dvd_sub_of_emod_eq rfl

@[simp]
lemma zmod_val_add_mod (n : ℕ) [NeZero n] (a b : ZMod n) :
    (n : ℤ) ∣ ((ZMod.val a : ℤ) + (ZMod.val b : ℤ) - (ZMod.val (a + b) : ℤ)) := by
  rw [Int.dvd_iff_emod_eq_zero, ZMod.val_add]
  simp only [Int.ofNat_emod, Nat.cast_mul, EuclideanDomain.mod_eq_zero]
  exact Int.dvd_sub_of_emod_eq rfl

lemma val_eq_val_of_val {n : ℕ} (x : ZMod n) :
    ZMod.val x = ZMod.val (ZMod.val x : ZMod n) := by
  simp only [ZMod.val_nat_cast]
  -- refine (Nat.mod_eq_of_lt ?h).symm
  if hn : n = 0 then
    simp only [hn, Nat.mod_zero]
  else
    refine (Nat.mod_eq_of_lt ?h).symm
    letI : NeZero n := { out := hn }
    exact ZMod.val_lt x

lemma residue_eq_of_val {n : ℕ} (x : ZMod n) (h : n > 0):
    x = (ZMod.val x) := by
  letI : NeZero n := NeZero.of_pos h
  refine zmod_val_sub_div_by_n_eq n x ↑(ZMod.val x) ?h
  rw [val_eq_val_of_val x]
  simp only [ZMod.nat_cast_val, ZMod.cast_id', id_eq, sub_self, dvd_zero]

lemma castHom_of_coe_eq_coe {m n : ℕ} (h : m ∣ n) (x : ℕ) :
    ZMod.castHom h (ZMod m) x = x := map_natCast (ZMod.castHom h (ZMod m)) x

lemma val_eqiv_val_of_residue' {m n : ℕ} (h : m ∣ n) (x : ZMod n) (hn : n > 0):
    ZMod.val (ZMod.castHom h (ZMod m) x) = ZMod.val x % m := by
  rw [residue_eq_of_val x hn]
  rw [castHom_of_coe_eq_coe]
  simp only [CharP.cast_eq_zero, mul_zero, zero_add, ZMod.val_nat_cast]
  exact (Nat.mod_mod_of_dvd _ h).symm

lemma val_eqiv_val_of_residue {m n : ℕ} (h : m ∣ n) (x : ZMod n) (hn : n > 0):
    (m : ℤ) ∣ ZMod.val x - ZMod.val (ZMod.castHom h (ZMod m) x) := by
  rw [val_eqiv_val_of_residue' h x hn]
  exact Nat.modEq_iff_dvd.mp (Nat.mod_modEq (ZMod.val x) m)

/-!
# Endormorphisms of Cyclic Groups
Defines

automorphism group of a finite cyclic group of order n is isomorphic to (Z/n)*
`MonoidHom.map_cyclic` yields the quotient representative
First we need mod n well-definedness
-/

@[to_additive (attr := simp) is_endToIntMul]
def is_endToIntPow {G : Type*} [Group G] (σ : G →* G) (n : ℤ) :=
  ∀ g : G, σ g = g ^ n

@[to_additive (attr := simp) is_endToMul]
def is_endToPow {G : Type*} [Group G] [Fintype G] [IsCyclic G] (σ : G →* G) (n : ZMod (Fintype.card G)) :=
  is_endToIntPow σ (ZMod.val n : ℤ)

-- @[to_additive (attr := simp) is_endToMul]
-- def is_endToPow {G : Type*} [Group G] [Fintype G] [IsCyclic G] (σ : G →* G) (n : ZMod (Fintype.card G)) :=
--   ∀ g : G, σ g = g ^ (ZMod.val n)

-- @[to_additive (attr := simp) is_endToMul_equiv_is_endToIntMul]
-- lemma is_endToPow_equiv_is_endToIntPow
--     {G : Type*} [Group G] [Fintype G] [IsCyclic G]
--       (σ : G →* G) (n : ZMod (Fintype.card G)) :
--         is_endToPow σ n ↔ is_endToIntPow σ (ZMod.val n) := by
--   simp only [is_endToPow]

-- @[to_additive (attr := simp) is_endToMul_iff_is_endToMul']
-- lemma is_endToPow_iff_is_endToPow' {G : Type*} [Group G] [Fintype G] [IsCyclic G] (σ : G →* G) (n : ZMod (Fintype.card G)) :
--     is_endToPow σ n ↔ is_endToPow' σ n := by
--   simp only [is_endToPow, is_endToIntPow, is_endToPow', zpow_natCast]

@[to_additive (attr := simp)]
lemma MonoidHom.map_cyclic_well_defined_mod_card {G : Type*} [Group G] [Fintype G] [h : IsCyclic G]
    {σ : Monoid.End G} {n m : ℤ} (hn : is_endToIntPow σ n) (hm : is_endToIntPow σ m) :
      ((Fintype.card G) : ℤ) ∣ (n - m) := by
  have h : ∀ g : G, g ^ (n - m) = 1 := by
    intro g
    rw [zpow_sub, ← hn, hm, @mul_inv_self]
  rw [← IsCyclic.exponent_eq_card]
  exact Group.exponent_dvd_of_forall_pow_eq_one G (n - m) h

@[to_additive (attr := simp) exists_endToIntMul]
lemma exists_endToIntPow {G : Type*} [Group G] [h : IsCyclic G] (σ : Monoid.End G) :
    ∃ n : ℤ, is_endToIntPow σ n := by
  obtain ⟨n, hn⟩ := MonoidHom.map_cyclic σ
  use n
  exact hn

@[to_additive (attr := simp) exists_endToMul]
lemma exists_endToPow {G : Type*} [Group G] [Fintype G] [h : IsCyclic G] (σ : Monoid.End G) :
    ∃ n : ZMod (Fintype.card G), is_endToPow σ n := by
  obtain ⟨m, hm⟩ := exists_endToIntPow σ
  let n := (m : ZMod (Fintype.card G))
  have hn : is_endToPow σ n := by
    simp only [is_endToPow, is_endToIntPow, ZMod.nat_cast_val]
    intro g
    rw [hm, ZMod.coe_int_cast m]
    exact (zpow_mod_card g m).symm
  use n

@[to_additive (attr := simp) unique_endToMul]
lemma unique_endToPow {G : Type*} [Group G] [Fintype G] [IsCyclic G]
    (σ : Monoid.End G) (m n : ZMod (Fintype.card G))
      (hm : is_endToPow σ m) (hn : is_endToPow σ n) :
        m = n :=
  zmod_val_sub_div_by_n_eq (Fintype.card G) m n (MonoidHom.map_cyclic_well_defined_mod_card hm hn)

@[to_additive (attr := simp) exists_unique_endToMul]
theorem exists_unique_endToPow {G : Type*} [Group G] [Fintype G] [h : IsCyclic G] (σ : G →* G) :
    ∃! n : ZMod (Fintype.card G), is_endToPow σ n := by
  obtain ⟨n, hn⟩ := exists_endToPow σ
  have hh : ∀ m : ZMod (Fintype.card G), is_endToPow σ m → m = n := by
    intro m hm
    exact unique_endToPow σ m n hm hn
  exact ExistsUnique.intro n hn hh

@[simp]
lemma is_endToPow_of_one {G : Type*} [Group G] [Fintype G] [IsCyclic G] :
    is_endToPow (MonoidHom.id G) (1 : ZMod (Fintype.card G)) := by
  dsimp only [is_endToPow, is_endToIntPow, MonoidHom.one_apply]
  intro g
  simp only [MonoidHom.id_apply]
  rw [(ZMod.val_one_eq_one_mod (Fintype.card G))]
  simp only [Int.ofNat_emod, zpow_mod_card, Nat.cast_one, zpow_one]

@[simp]
lemma is_endToMul_of_one {G : Type*} [AddGroup G] [Fintype G] [IsAddCyclic G] :
    is_endToMul (AddMonoidHom.id G) (1 : ZMod (Fintype.card G)) := by
  dsimp only [is_endToMul, is_endToIntMul, AddMonoidHom.id_apply]
  intro g
  rw [(ZMod.val_one_eq_one_mod (Fintype.card G))]
  simp only [Int.ofNat_emod, mod_card_zsmul, Nat.cast_one, one_zsmul]

@[simp]
lemma is_endToPow_of_mul {G : Type*} [Group G] [Fintype G] [h : IsCyclic G]
    {σ τ : Monoid.End G} {m n : ZMod (Fintype.card G)}
      (hm : is_endToPow σ m) (hn : is_endToPow τ n) :
        is_endToPow (σ * τ) (m * n) := by
  intro g
  rw [Monoid.coe_mul, Function.comp_apply, hm, hn]
  have : ((Monoid.exponent G) : ℤ) ∣ ((ZMod.val m : ℤ) * (ZMod.val n : ℤ) - (ZMod.val (m * n) : ℤ)) := by
    rw [IsCyclic.exponent_eq_card]
    exact zmod_val_mul_mod (Fintype.card G) m n
  rw [← zpow_mul, Nat.cast_comm]
  exact pow_eq_pow_of_order_dvd_dif g ((ZMod.val m : ℤ) * (ZMod.val n : ℤ)) (ZMod.val (m * n)) this

@[simp]
lemma is_endToMul_of_mul {G : Type*} [AddGroup G] [Fintype G] [h : IsAddCyclic G]
    {σ τ : AddMonoid.End G} {m n : ZMod (Fintype.card G)}
      (hm : is_endToMul σ m) (hn : is_endToMul τ n) :
        is_endToMul (σ * τ) (m * n) := by
  intro g
  rw [AddMonoid.coe_mul, Function.comp_apply, hm, hn]
  have : ((AddMonoid.exponent G) : ℤ) ∣ ((ZMod.val m : ℤ) * (ZMod.val n : ℤ) - (ZMod.val (m * n) : ℤ)) := by
    rw [IsAddCyclic.exponent_eq_card]
    exact zmod_val_mul_mod (Fintype.card G) m n
  rw [← mul_zsmul', Nat.cast_comm]
  exact nsmul_eq_nsmul_of_order_dvd_dif g ((ZMod.val m : ℤ) * (ZMod.val n : ℤ)) (ZMod.val (m * n)) this

instance {G : Type*} [AddGroup G] [IsAddCyclic G] : AddCommGroup G := IsAddCyclic.addCommGroup

@[simp]
lemma is_endToMul_of_add {G : Type*} [AddGroup G] [Fintype G] [h : IsAddCyclic G]
    {σ τ : AddMonoid.End G} {m n : ZMod (Fintype.card G)}
      (hm : is_endToMul σ m) (hn : is_endToMul τ n) :
        is_endToMul (σ + τ) (m + n) := by
  intro g
  have a : (σ + τ) g = σ g + τ g := by rfl
  rw [a, hn, hm, ←add_zsmul]
  have : ((AddMonoid.exponent G) : ℤ) ∣ ((ZMod.val m : ℤ) + (ZMod.val n : ℤ) - (ZMod.val (m + n) : ℤ)) := by
    rw [IsAddCyclic.exponent_eq_card]
    exact zmod_val_add_mod (Fintype.card G) m n
  exact nsmul_eq_nsmul_of_order_dvd_dif g ((ZMod.val m : ℤ) + (ZMod.val n : ℤ)) (ZMod.val (m + n)) this

@[to_additive (attr := simp) endToMulFun]
noncomputable def endToPowFun {G : Type*} [Group G] [Fintype G] [IsCyclic G] (σ : Monoid.End G) :
    ZMod (Fintype.card G) :=
  Exists.choose (exists_unique_endToPow σ)

@[to_additive (attr := simp) endToMulFun_spec]
def endToPowFun_spec {G : Type*} [Group G] [Fintype G] [IsCyclic G] (σ : Monoid.End G) :=
  Exists.choose_spec (exists_unique_endToPow σ)

-- endToPow statisfies the predicate is_endToPow
@[to_additive (attr := simp) is_endToMul_endToMulFun]
lemma is_endToPow_endToPowFun {G : Type*} [Group G] [Fintype G] [IsCyclic G] (σ : Monoid.End G) :
    is_endToPow σ (endToPowFun σ) :=
  (endToPowFun_spec σ).left

-- is_endToPow is uniquely satisfied by endToPow
@[to_additive (attr := simp) is_endToMul_equal_endToMulFun]
lemma is_endToPow_equal_endToPowFun {G : Type*} [Group G] [Fintype G] [IsCyclic G] {σ : Monoid.End G}
    {n : ZMod (Fintype.card G)} (h : is_endToPow σ n) :
       n = endToPowFun σ :=
  (endToPowFun_spec σ).right n h

@[simp]
lemma endToPow_map_one {G : Type*} [Group G] [Fintype G] [IsCyclic G] :
    endToPowFun 1 = (1 : ZMod (Fintype.card G)) :=
  (is_endToPow_equal_endToPowFun is_endToPow_of_one).symm

@[simp]
lemma endToMul_map_one {G : Type*} [AddGroup G] [Fintype G] [IsAddCyclic G] :
    endToMulFun 1 = (1 : ZMod (Fintype.card G)) :=
  (is_endToMul_equal_endToMulFun is_endToMul_of_one).symm

@[simp]
lemma endToPow_map_mul {G : Type*} [Group G] [Fintype G] [IsCyclic G] (σ τ : Monoid.End G) :
    endToPowFun (σ * τ) = (endToPowFun σ) * (endToPowFun τ) :=
  (is_endToPow_equal_endToPowFun (is_endToPow_of_mul (is_endToPow_endToPowFun σ) (is_endToPow_endToPowFun τ))).symm

@[simp]
lemma endToMul_map_mul {G : Type*} [AddGroup G] [Fintype G] [IsAddCyclic G] (σ τ : AddMonoid.End G) :
    endToMulFun (σ * τ) = (endToMulFun σ) * (endToMulFun τ) :=
  (is_endToMul_equal_endToMulFun (is_endToMul_of_mul (is_endToMul_endToMulFun σ) (is_endToMul_endToMulFun τ))).symm

@[to_additive (attr := simp) mulToEndFun]
def powToEndFun {G : Type*} [Group G] [Fintype G] [IsCyclic G] (n : ZMod (Fintype.card G)) : Monoid.End G :=
  { toFun := fun g => g ^ ZMod.val n
    map_one' := one_pow (ZMod.val n)
    map_mul' := by
      intro g h
      group
      refine Commute.mul_zpow ?h ↑(ZMod.val n)
      refine (commute_iff_eq g h).mpr ?h.a
      exact IsCyclic.commGroup.proof_1 g h

      -- have hc : CommGroup G := IsCyclic.commGroup
      -- have := mul_pow g h (ZMod.val n)
  }

@[to_additive (attr := simp) is_endToMul_of_mulToEndFun]
lemma is_endToPow_of_powToEndFun {G : Type*} [Group G] [Fintype G] [IsCyclic G] (n : ZMod (Fintype.card G)):
    is_endToPow (powToEndFun n) n :=
  fun g => (zpow_natCast g (ZMod.val n)).symm

@[to_additive endToMul_left_inv]
lemma endToPow_left_inv {G : Type*} [Group G] [Fintype G] [IsCyclic G] :
    @Function.LeftInverse (Monoid.End G) _ powToEndFun endToPowFun := by
  rw [Function.leftInverse_iff_comp]
  ext σ
  simp only [Function.comp_apply, id_eq]
  apply MonoidHom.ext
  intro g
  simp only [is_endToPow_endToPowFun σ g, zpow_natCast, powToEndFun, endToPowFun, OneHom.coe_mk, MonoidHom.coe_mk]

@[to_additive endToMul_right_inv]
lemma endToPow_right_inv {G : Type*} [Group G] [Fintype G] [IsCyclic G] :
    @Function.RightInverse (Monoid.End G) _ powToEndFun endToPowFun := by
  rw [Function.rightInverse_iff_comp]
  ext n
  exact (is_endToPow_equal_endToPowFun (is_endToPow_of_powToEndFun n)).symm

@[simp]
noncomputable def endToPow {G : Type*} [Group G] [Fintype G] [IsCyclic G] :
  (Monoid.End G) ≃* ZMod (Fintype.card G) where
    toFun := endToPowFun
    invFun := powToEndFun
    left_inv := endToPow_left_inv
    right_inv := endToPow_right_inv
    map_mul' := endToPow_map_mul

@[simp]
lemma endToMul_map_add {G : Type*} [AddGroup G] [Fintype G] [IsAddCyclic G] (σ τ : AddMonoid.End G) :
    endToMulFun (σ + τ) = (endToMulFun σ) + (endToMulFun τ) :=
  (is_endToMul_equal_endToMulFun (is_endToMul_of_add (is_endToMul_endToMulFun σ) (is_endToMul_endToMulFun τ))).symm

@[simp]
noncomputable def endToMul {G : Type*} [AddGroup G] [Fintype G] [IsAddCyclic G] :
  (AddMonoid.End G) ≃+* ZMod (Fintype.card G) where
    toFun := endToMulFun
    invFun := mulToEndFun
    left_inv := endToMul_left_inv
    right_inv := endToMul_right_inv
    map_mul' := endToMul_map_mul
    map_add' := endToMul_map_add

-- TODO : additive version
-- @[to_additive (attr := simp) end_restict_to_cyclic_subgroup']
lemma end_restict_to_cyclic_subgroup {G: Type*} [Group G] {H H' : Subgroup G} [IsCyclic H]
      (h : H' ≤ H) (σ : Monoid.End H) (x : H') :
    (σ (SubgroupClass.inclusion h x) : G) ∈ H' := by
  obtain ⟨n, h⟩ := exists_endToIntPow σ
  rw [h]
  simp only [SubgroupClass.coe_zpow, SubgroupClass.coe_inclusion]
  exact Subgroup.zpow.proof_1 H' x n

-- TODO : additive version
@[simp]
def restrictEndtoSubgroup {G: Type*} [Group G]
    {H H' : Subgroup G} [IsCyclic H]
      (h : H' ≤ H) :
        Monoid.End H →* Monoid.End H' where
  toFun := fun σ => {
    toFun := fun x => ⟨σ (SubgroupClass.inclusion h x), end_restict_to_cyclic_subgroup h σ x⟩
    map_one' := by
      simp only [map_one, OneMemClass.coe_one, Submonoid.mk_eq_one]
    map_mul' := by
      simp only [map_mul, Submonoid.coe_mul, Subgroup.coe_toSubmonoid, Submonoid.mk_mul_mk,
        Subtype.forall, implies_true, forall_const]
  }
  map_one' := rfl
  map_mul' := fun _ _ => rfl

-- TODO : additive version
@[simp]
lemma is_endToPow_of_residue_res_subgroup {G: Type*} [Group G] {H H' : Subgroup G}
      [Fintype H] [IsCyclic H]
        [Fintype H'] [IsCyclic H']
          (h : H' ≤ H) (σ : Monoid.End H):
    is_endToPow (restrictEndtoSubgroup h σ)
      (ZMod.castHom (Subgroup.card_dvd_of_le h) (ZMod (Fintype.card H')) (endToPow σ)) := by
  intro g
  apply Subgroup.inclusion_injective h
  have this : Subgroup.inclusion h ((restrictEndtoSubgroup h σ) g) = σ (Subgroup.inclusion h g) := by
    rfl
  rw [this]
  have this' : σ (Subgroup.inclusion h g) = (Subgroup.inclusion h g) ^ ((ZMod.val (endToPow σ)) : ℤ) := by
    apply is_endToPow_endToPowFun
  rw [this']
  have this'' : (Subgroup.inclusion h) g ^ (ZMod.val (endToPow σ) : ℤ) = (Subgroup.inclusion h) (g ^ (ZMod.val (endToPow σ) : ℤ)) := by
    rfl
  rw [this'']
  apply congrArg (Subgroup.inclusion h)
  apply pow_eq_pow_of_order_dvd_dif
  rw [IsCyclic.exponent_eq_card]
  apply val_eqiv_val_of_residue _ _ Fintype.card_pos

-- TODO : additive version
@[simp]
lemma endToPow_compat_with_subgroup {G: Type*} [Group G] {H H' : Subgroup G}
      [Fintype H] [IsCyclic H]
        [Fintype H'] [IsCyclic H']
          (h : H' ≤ H) :
    MonoidHom.comp (ZMod.castHom (Subgroup.card_dvd_of_le h) (ZMod (Fintype.card H'))) endToPow.toMonoidHom
      = endToPow.toMonoidHom.comp (restrictEndtoSubgroup h):= by
  ext
  apply is_endToPow_equal_endToPowFun
  apply is_endToPow_of_residue_res_subgroup

/-!
# Modular Cyclotomic Character
-/

-- TODO : maybe genralize?
def monoidEndtoUnitEnd {M : Type*} [CommMonoid M]:
  Monoid.End M →* Monoid.End Mˣ where
    toFun := fun σ => {
      toFun := fun x => {
        val := σ x
        inv := σ x.inv
        val_inv := by rw [← map_mul, Units.val_inv, map_one]
        inv_val := by rw [← map_mul, Units.inv_val, map_one]
      }
      map_one' := by
        ext
        simp only [Units.val_one, map_one]
      map_mul' := by
        intros x y
        ext
        simp only [Units.val_mul, map_mul]
    }
    map_one' := rfl
    map_mul' := fun _ _ => rfl

def unitEndToRootsOfUnityEnd (k : ℕ+) {M : Type*} [CommMonoid M]:
  Monoid.End Mˣ →* Monoid.End (rootsOfUnity k M) where
    toFun := fun σ => {
      toFun := fun x => ⟨σ x, by
        rw [mem_rootsOfUnity, ← map_pow, x.2, map_one]
      ⟩
      map_one' := by
        simp only [MonoidHom.map_one]
        exact Subtype.ext (MonoidHom.map_one σ)
      map_mul' := by
        intro x y
        simp only [MonoidHom.map_mul]
        exact Subtype.ext (MonoidHom.map_mul σ x.1 y.1)
    }
    map_one' := rfl
    map_mul' := fun _ _ => rfl

noncomputable def ModularCyclotomicCharacter (R : Type*) [CommRing R] [IsDomain R] (n : ℕ+):
    Monoid.End R →* ZMod (Fintype.card (rootsOfUnity n R)) :=
  endToPow.toMonoidHom.comp <| (unitEndToRootsOfUnityEnd n).comp monoidEndtoUnitEnd

lemma rootsOfUnity_card_dvd_of_dvd (R : Type*) [CommRing R] [IsDomain R] {n m : ℕ+} (h : n ∣ m):
    Fintype.card (rootsOfUnity n R) ∣ Fintype.card (rootsOfUnity m R) :=
  Subgroup.card_dvd_of_le <| @rootsOfUnity_le_of_dvd R _ _ _ h

lemma modularCyclotomicCharacter_compat (R : Type*) [CommRing R] [IsDomain R] {n m : ℕ+} (h : n ∣ m) :
    MonoidHom.comp (ZMod.castHom (rootsOfUnity_card_dvd_of_dvd R h) (ZMod (Fintype.card (rootsOfUnity n R))))
      (ModularCyclotomicCharacter R m) =
        (ModularCyclotomicCharacter R n) := by
  dsimp only [ModularCyclotomicCharacter]
  rw [← MonoidHom.comp_assoc, ← MonoidHom.comp_assoc, ← MonoidHom.comp_assoc, endToPow_compat_with_subgroup (rootsOfUnity_le_of_dvd h)]
  rfl

/-!
# p-adic Cyclotomic Character
-/

def PadicInt.unitLift {p : ℕ} [hp_prime : Fact (Nat.Prime p)] {G : Type*} [Group G]
  {f : (k : ℕ) → G →* ZMod (p ^ k)}
    (f_compat :
      ∀ (k1 k2 : ℕ) (hk : k1 ≤ k2),
        MonoidHom.comp (ZMod.castHom (Nat.pow_dvd_pow p hk) (ZMod (p ^ k1))) (f k2) = f k1) :
          G →* ℤ_[p] := sorry

noncomputable def cyclotomic_character (K : Type*) [Field K] (l p : ℕ) [CharP K p] [Fact (Nat.Prime l)] (h : l ≠ p) :
    Field.absoluteGaloisGroup K →* PadicInt l :=
  sorry
