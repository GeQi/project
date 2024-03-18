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

-- automorphism group of a finite cyclic group of order n is isomorphic to (Z/n)*
-- `MonoidHom.map_cyclic` yields the quotient representative
-- First we need mod n well-definedness

@[to_additive (attr := simp)]
theorem Group.exponent_dvd_of_forall_pow_eq_one (G : Type*) [Group G] (n : ℤ)
      (hG : ∀ (g : G), g ^ n = 1) :
    ((Monoid.exponent G) : ℤ) ∣ n := by
  match n with
  | Int.ofNat m =>
    have h : ∀ g : G, g ^ m = 1 := by
      intro g
      rw [← zpow_coe_nat]
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

@[to_additive (attr := simp) is_endToIntMul]
def is_endToIntPow {G : Type*} [Group G] [Fintype G] [IsCyclic G] (σ : G →* G) (n : ℤ) :=
  ∀ g : G, σ g = g ^ n

@[to_additive (attr := simp) is_endToMul]
def is_endToPow {G : Type*} [Group G] [Fintype G] [IsCyclic G] (σ : G →* G) (n : ZMod (Fintype.card G)) :=
  is_endToIntPow σ (ZMod.val n)

@[to_additive (attr := simp) is_endToMul_equiv_is_endToIntMul]
lemma is_endToPow_equiv_is_endToIntPow
    {G : Type*} [Group G] [Fintype G] [IsCyclic G]
      (σ : G →* G) (n : ZMod (Fintype.card G)) :
        is_endToPow σ n ↔ is_endToIntPow σ (ZMod.val n) := by
  simp only [is_endToPow]

@[to_additive (attr := simp)]
lemma MonoidHom.map_cyclic_well_defined_mod_card {G : Type*} [Group G] [Fintype G] [h : IsCyclic G]
    {σ : G →* G} {n m : ℤ} (hn : is_endToIntPow σ n) (hm : is_endToIntPow σ m) :
      ((Fintype.card G) : ℤ) ∣ (n - m) := by
  have h : ∀ g : G, g ^ (n - m) = 1 := by
    intro g
    rw [zpow_sub, ← hn, hm, @mul_inv_self]
  rw [← IsCyclic.exponent_eq_card]
  exact Group.exponent_dvd_of_forall_pow_eq_one G (n - m) h

@[to_additive (attr := simp) exists_endToIntMul]
lemma exists_endToIntPow {G : Type*} [Group G] [Fintype G] [h : IsCyclic G] (σ : Monoid.End G) :
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

lemma zero_of_bounded_divisor {d n : ℤ} (h1 : -n < d) (h2 : d < n) (h3 : n ∣ d): d = 0 := by
  obtain ⟨c, hc⟩ := h3
  rw [hc] at h1 h2
  have : c = 0 := by nlinarith
  rw [this] at hc
  simp only [mul_zero] at hc
  exact hc

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

@[to_additive]
lemma pow_eq_one_of_order_dvd {G : Type*} [Group G] (g: G) (a: ℤ)
    (hh : (Monoid.exponent G : ℤ) ∣ a) : g ^ a = 1 := by
  obtain ⟨c, hc⟩ := hh
  rw [hc, zpow_mul, zpow_coe_nat, Monoid.pow_exponent_eq_one, one_zpow]

@[to_additive]
lemma pow_eq_pow_of_order_dvd_dif {G : Type*} [Group G] (g: G) (a b: ℤ)
    (h : (Monoid.exponent G : ℤ) ∣ a - b) : g ^ a = g ^ b := by
  obtain ⟨c, hc⟩ := h
  have : g ^ (a - b) = 1 := by
    apply pow_eq_one_of_order_dvd g (a - b) _
    exact Exists.intro c hc
  rwa [← mul_inv_eq_one, ← zpow_sub]

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

-- TODO: name
instance inst_riring {G : Type*} [AddGroup G] [IsAddCyclic G] : AddCommGroup G := IsAddCyclic.addCommGroup

@[simp]
lemma is_endToMul_of_add {G : Type*} [AddGroup G] [Fintype G] [h : IsAddCyclic G]
    {σ τ : AddMonoid.End G} {m n : ZMod (Fintype.card G)}
      (hm : is_endToMul σ m) (hn : is_endToMul τ n) :
        is_endToMul (σ + τ) (m + n) := by
  intro g
  letI : NeZero (AddMonoid.exponent G) := by
    sorry
  sorry

@[to_additive (attr := simp) endToMulFun]
noncomputable def endToPowFun {G : Type*} [Group G] [Fintype G] [IsCyclic G] (σ : Monoid.End G) :
    ZMod (Fintype.card G) :=
  Exists.choose (exists_unique_endToPow σ)

@[to_additive (attr := simp) endToMulFun_spec]
def endToPowFun_spec {G : Type*} [Group G] [Fintype G] [IsCyclic G] (σ : Monoid.End G) :=
  Exists.choose_spec (exists_unique_endToPow σ)

@[to_additive (attr := simp) is_endToMul_endToMulFun]
lemma is_endToPow_endToPowFun {G : Type*} [Group G] [Fintype G] [IsCyclic G] (σ : Monoid.End G) :
    is_endToPow σ (endToPowFun σ) :=
  (endToPowFun_spec σ).left

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
  fun g => (zpow_coe_nat g (ZMod.val n)).symm

@[to_additive endToMul_left_inv]
lemma endToPow_left_inv {G : Type*} [Group G] [Fintype G] [IsCyclic G] :
    @Function.LeftInverse (Monoid.End G) _ powToEndFun endToPowFun := by
  rw [Function.leftInverse_iff_comp]
  ext σ
  simp only [Function.comp_apply, id_eq]
  apply MonoidHom.ext
  intro g
  simp only [is_endToPow_endToPowFun σ g, zpow_coe_nat, powToEndFun, endToPowFun, OneHom.coe_mk, MonoidHom.coe_mk]

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

@[to_additive (attr := simp) res_image']
lemma res_image {G: Type*} [Group G] [Fintype G] [IsCyclic G]
    (σ : Monoid.End G) (H : Subgroup G) : (MonoidHom.restrict σ H).range ≤ H := by
  rw [@MonoidHom.restrict_range, @SetLike.le_def]
  intro x hx
  rw [@Subgroup.mem_map] at hx
  obtain ⟨n, hn⟩ := exists_endToPow σ
  obtain ⟨y, ⟨h1, h2⟩⟩ := hx
  dsimp at hn
  rw [hn] at h2
  rw [← h2]
  exact Subgroup.zpow_mem H h1 ↑(ZMod.val n)

@[to_additive (attr := simp)]
def restrictEndtoSubgroup {G: Type*} [Group G] [Fintype G] [IsCyclic G]
    (H : Subgroup G) (σ : Monoid.End G) : Monoid.End H :=
  (Subgroup.inclusion (res_image σ H)).comp (MonoidHom.rangeRestrict (MonoidHom.restrict σ H))

-- @[to_additive (attr := simp)]
@[simp]
def restrictEndtoSubgroup' {G: Type*} [Group G] [Fintype G] [IsCyclic G]
    (H : Subgroup G) (σ : Monoid.End G) : Monoid.End H where
  toFun := fun h => ⟨σ h, by
    apply res_image σ H
    exact ⟨h, rfl⟩
    ⟩
  map_one' := by
    refine (Submonoid.mk_eq_one H.toSubmonoid).mpr ?_
    exact OneHom.copy.proof_1 (↑σ) (⇑σ) rfl
  map_mul' := by
    sorry

-- @[to_additive (attr := simp)]
-- def restrictEndtoSubgroup_same {G: Type*} [Group G] [Fintype G] [IsCyclic G]
--     (H : Subgroup G) (σ : Monoid.End G) (g : H): (restrictEndtoSubgroup H σ) g = σ g := by
--   simp only [restrictEndtoSubgroup]
--   sorry

@[to_additive (attr := simp) inst_this']
instance inst_this {G: Type*} [Group G] [Fintype G] (H : Subgroup G) : Fintype H := sorry

@[to_additive (attr := simp)]
lemma subgroup_card_div_card {G: Type*} [Group G] [Fintype G] [IsCyclic G]
    (H : Subgroup G) : Fintype.card H ∣ Fintype.card G := by
  sorry

lemma eq_smth'' {m n : ℕ} (h : m ∣ n) (x : ZMod n):
    ZMod.val (ZMod.castHom h (ZMod m) x) = ZMod.val x % m := by
  match n with
  | 0 => sorry
  | k+1 => sorry


lemma eq_smth {m n : ℕ} (h : m ∣ n) (x : ZMod n):
    (m : ℤ) ∣ ZMod.val (ZMod.castHom h (ZMod m) x) - ZMod.val x := by
  rw [eq_smth'']
  refine Nat.modEq_iff_dvd.mp ?_
  exact Nat.ModEq.symm (Nat.mod_modEq (ZMod.val x) m)

-- lemma llll {G: Type*} [Group G] [Fintype G] [IsCyclic G] (g : G) (n : ℕ):
--     g ^ n = g ^ (n % (Fintype.card G)) := by
--   exact (pow_mod_card g n).symm
--   exact (zpow_mod_card g n).symm

lemma gggg {G: Type*} [Group G] (g : G) (n : ℕ):
    g ^ n = g ^ (n : ℤ) := by
  exact (zpow_coe_nat g n).symm

set_option maxHeartbeats 0
lemma is_endToPow_bla {G: Type*} [Group G] [Fintype G] [IsCyclic G] (H : Subgroup G) (σ : Monoid.End G) :
    is_endToPow (restrictEndtoSubgroup' H σ) (((ZMod.castHom (subgroup_card_div_card H) (ZMod (Fintype.card H))) ∘ endToPow) σ) := by
  intro g
  simp only [restrictEndtoSubgroup', MonoidHom.coe_mk, OneHom.coe_mk]
  simp only [Function.comp_apply]
  -- simp only [restrictEndtoSubgroup', MonoidHom.coe_mk, OneHom.coe_mk, inst_this, endToPow,
  --   MulEquiv.coe_mk, Equiv.coe_fn_mk, Function.comp_apply, endToPowFun, is_endToPow,
  --   ZMod.nat_cast_val, is_endToIntPow, ZMod.castHom_apply]

  rw [eq_smth'']
  rw [zpow_coe_nat]
  rw [pow_mod_card]
  rw [← zpow_coe_nat]
  apply Subtype.coe_eq_of_eq_mk
  apply is_endToPow_endToPowFun

@[simp]
lemma endToPow_compat_with_subgroup {G: Type*} [Group G] [Fintype G] [IsCyclic G] (H : Subgroup G) :
    ((ZMod.castHom (subgroup_card_div_card H) (ZMod (Fintype.card H))) ∘ endToPow)
      = endToPow ∘ (restrictEndtoSubgroup' H) := by
  ext σ
  apply is_endToPow_equal_endToPowFun
  apply is_endToPow_bla

lemma endToMul_compat_with_addSubgroup {G: Type*} [AddGroup G] [Fintype G] [IsAddCyclic G] (H : AddSubgroup G) :
    ((ZMod.castHom (addSubgroup_card_sub_card H) (ZMod (Fintype.card H))) ∘ endToMul)
      = endToMul ∘ (restrictEndtoAddSubgroup H) := by
  sorry

-- def PadicInt.lift' {p : ℕ} [hp_prime : Fact (Nat.Prime p)] {G : Type*} [AddGroup G]
--     {f : (k : ℕ) → G →+ ZMod (p ^ k)}
--       (f_compat : ∀ (k1 k2 : ℕ) (hk : k1 ≤ k2),
--         AddMonoidHom.comp (ZMod.castHom (Nat.pow_dvd_pow p hk) (ZMod (p ^ k1))) (f k2) = f k1) :
--           G →+ ℤ_[p] :=
--   sorry

-- absoluteGaloisGroup acts on the mul group of l^k roots of unity
def absGalToRootsOfUnityEnd (K : Type*) [Field K] {l p : ℕ} [CharP K p] [Fact (Nat.Prime l)] (h : l ≠ p)
    (k : ℕ) : (Field.absoluteGaloisGroup K) →* (Monoid.End (rootsOfUnity (⟨l, Fin.size_pos'⟩^k) (AlgebraicClosure K))) where
  toFun := sorry
  map_one' := sorry
  map_mul' := sorry

def addAbsGalToRootsOfUnityAddEnd (K : Type*) [Field K] {l p : ℕ} [CharP K p] [Fact (Nat.Prime l)] (h : l ≠ p)
    (k : ℕ) : Additive (Field.absoluteGaloisGroup K) →+ (AddMonoid.End (Additive (rootsOfUnity (⟨l, Fin.size_pos'⟩^k) (AlgebraicClosure K)))) := sorry

lemma card_of_rootsOfUnity (K : Type*) [Field K] {l p : ℕ} [CharP K p] [Fact (Nat.Prime l)] (h : l ≠ p)
    (k : ℕ) : Fintype.card (rootsOfUnity (⟨l, Fin.size_pos'⟩^k) (AlgebraicClosure K)) = l ^ k := by
  sorry

-- def fixZMod (K : Type*) [Field K] {l p : ℕ} [CharP K p] [Fact (Nat.Prime l)] (h : l ≠ p)
--     (k : ℕ) : ZMod (Fintype.card (rootsOfUnity (⟨l, Fin.size_pos'⟩^k) (AlgebraicClosure K))) →+ ZMod (l ^ k) :=
--   sorry

-- noncomputable def f (K : Type*) [Field K] {l p : ℕ} [CharP K p] [Fact (Nat.Prime l)] (h : l ≠ p)
--     (k : ℕ) : Additive (Field.absoluteGaloisGroup K) →+ ZMod (l ^ k) := sorry
--   -- (fixZMod K h k).comp (endToMul.toAddMonoidHom.comp (addAbsGalToRootsOfUnityAddEnd K h k))

-- lemma f_compat {K : Type*} [Field K] {l p : ℕ} [CharP K p] [Fact (Nat.Prime l)] (h : l ≠ p)
--     (k1 k2 : ℕ) (hk : k1 ≤ k2) :
--       AddMonoidHom.comp (ZMod.castHom (Nat.pow_dvd_pow l hk) (ZMod (l ^ k1))) (f K h k2) = f K h k1 := by
--   -- ext σ
--   -- rw [f]
--   -- dsimp
--   sorry

noncomputable def cyclotomic_chracter (K : Type*) [Field K] (l p : ℕ) [CharP K p] [Fact (Nat.Prime l)] (h : l ≠ p) :
    Field.absoluteGaloisGroup K →* PadicInt l :=
  -- PadicInt.lift' (f_compat h)
  sorry
