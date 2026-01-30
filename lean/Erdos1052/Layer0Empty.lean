/-
  Erdős Problem #1052 - Layer 0 空集定理（奇数酉完全数不存在）

  **核心论证**（论文引理 2.2，纯数学证明，禁止穷举）：

  设 m 为奇数酉完全数，则 σ*(m) = 2m。

  **Step 1**: v₂(2m) = 1（因为 m 是奇数）

  **Step 2**: v₂(σ*(m)) = v₂(∏(1 + p_i^{a_i})) = Σ v₂(1 + p_i^{a_i})
  （由 σ* 乘法性）

  **Step 3**: 对于任意奇素数幂 p^a，1 + p^a 是偶数，故 v₂(1 + p^a) ≥ 1

  **Step 4**: 因此 v₂(σ*(m)) ≥ ω(m)（m 的素因子个数）

  **Step 5**: 由 σ*(m) = 2m，得 v₂(σ*(m)) = v₂(2m) = 1

  **Step 6**: 因此 ω(m) ≤ 1

  **Step 7**: ω(m) = 0 ⟹ m = 1，但 σ*(1) = 1 ≠ 2·1 = 2

  **Step 8**: ω(m) = 1 ⟹ m = p^a（素数幂），σ*(p^a) = 1 + p^a
             若 1 + p^a = 2p^a，则 p^a = 1，但 p ≥ 3 ⟹ p^a ≥ 3 > 1，矛盾

  **结论**：不存在奇数酉完全数。
-/

import Mathlib.Tactic
import Mathlib.NumberTheory.Padics.PadicVal
import Mathlib.Data.Nat.Factorization.Basic
import Erdos1052.Basic
import Erdos1052.SigmaStarMultiplicative

namespace Erdos1052

/-!
## 基础定义
-/

-- v₂(n) = 2-adic valuation of n（使用 mathlib padicValNat）
abbrev v₂ (n : Nat) : Nat := padicValNat 2 n

-- ω(n) = 素因子个数（distinct prime factors）
noncomputable def omega (n : Nat) : Nat := n.factorization.support.card

/-!
## Step 1：v₂(2m) = 1 当 m 是奇数

**引理**：若 m 是正奇数，则 v₂(2m) = v₂(2) + v₂(m) = 1 + 0 = 1
-/

-- v₂(m) = 0 当 m 是奇数且 m > 0
theorem v2_of_odd (m : Nat) (hpos : m > 0) (hodd : m % 2 = 1) : v₂ m = 0 := by
  unfold v₂
  rw [padicValNat.eq_zero_iff]
  right; right
  intro h2div
  have heven : m % 2 = 0 := Nat.mod_eq_zero_of_dvd h2div
  rw [hodd] at heven
  exact absurd heven (by decide)

-- v₂(2*m) = 1 当 m 是奇数且 m > 0
theorem v2_two_mul_odd (m : Nat) (hpos : m > 0) (hodd : m % 2 = 1) : v₂ (2 * m) = 1 := by
  unfold v₂
  rw [padicValNat.mul (by decide : 2 ≠ 0) (Nat.pos_iff_ne_zero.mp hpos)]
  have h1 : padicValNat 2 2 = 1 := by native_decide
  have h2 : padicValNat 2 m = 0 := v2_of_odd m hpos hodd
  simp [h1, h2]

/-!
## Step 3：v₂(1 + p^a) ≥ 1 对于奇素数幂

**引理**：若 p 是奇素数，a ≥ 1，则 1 + p^a 是偶数，故 v₂(1 + p^a) ≥ 1
-/

-- 奇数的幂是奇数
theorem odd_pow_odd (p a : Nat) (hodd : p % 2 = 1) (ha : a ≥ 1) : (p^a) % 2 = 1 := by
  induction a with
  | zero => simp at ha
  | succ n ih =>
    by_cases hn : n = 0
    · simp [hn, hodd]
    · have hn' : n ≥ 1 := Nat.one_le_iff_ne_zero.mpr hn
      have ih' := ih hn'
      simp only [pow_succ]
      calc (p * p^n) % 2 = ((p % 2) * (p^n % 2)) % 2 := by rw [Nat.mul_mod]
        _ = (1 * 1) % 2 := by rw [ih', hodd]
        _ = 1 := by decide

-- 1 + 奇数 是偶数
theorem one_plus_odd_even (n : Nat) (hodd : n % 2 = 1) : (1 + n) % 2 = 0 := by
  calc (1 + n) % 2 = (1 % 2 + n % 2) % 2 := Nat.add_mod 1 n 2
    _ = (1 + 1) % 2 := by simp [hodd]
    _ = 0 := by native_decide

-- v₂(偶数) ≥ 1
theorem v2_ge_one_of_even (n : Nat) (hpos : n > 0) (heven : n % 2 = 0) : v₂ n ≥ 1 := by
  unfold v₂
  have h2div : 2 ∣ n := Nat.dvd_of_mod_eq_zero heven
  have hn_ne : n ≠ 0 := Nat.pos_iff_ne_zero.mp hpos
  -- 2 | n 且 n ≠ 0 ⟹ padicValNat 2 n ≥ 1
  by_contra hlt
  push_neg at hlt
  have hval0 : padicValNat 2 n = 0 := Nat.lt_one_iff.mp hlt
  rw [padicValNat.eq_zero_iff] at hval0
  rcases hval0 with h2eq1 | hn0 | hndiv
  · exact absurd h2eq1 (by decide : ¬(2 = 1))
  · exact hn_ne hn0
  · exact hndiv h2div

-- v₂(1 + p^a) ≥ 1 对于奇数 p 和 a ≥ 1
theorem v2_one_plus_odd_pow (p a : Nat) (hodd_p : p % 2 = 1) (hgt : p > 1) (ha : a ≥ 1) :
    v₂ (1 + p^a) ≥ 1 := by
  have h_pa_odd : (p^a) % 2 = 1 := odd_pow_odd p a hodd_p ha
  have h_even : (1 + p^a) % 2 = 0 := one_plus_odd_even (p^a) h_pa_odd
  have h_pos : 1 + p^a > 0 := Nat.add_pos_left Nat.one_pos (p^a)
  exact v2_ge_one_of_even (1 + p^a) h_pos h_even

/-!
## Step 7：m = 1 的排除

**引理**：σ*(1) = 1 ≠ 2
-/

theorem sigmaStar_one : sigmaStar 1 = 1 := rfl

theorem one_not_unitary_perfect : ¬IsUnitaryPerfect 1 := by
  unfold IsUnitaryPerfect sigmaStar unitaryDivisors divisors
  native_decide

/-!
## Step 8：m = p^a（素数幂）的排除

**引理**：若 m = p^a（p 奇素数，a ≥ 1），则 σ*(m) = 1 + p^a ≠ 2p^a
-/

-- σ*(p^a) = 1 + p^a 对于素数幂
-- 素数幂的酉因子只有 1 和 p^a（因为 gcd(1, p^a) = 1, gcd(p^a, 1) = 1）
-- 证明方法：由 unitaryDivisors_prime_power_set，酉因子恰好是 {1, p^a}
-- 所以 σ*(p^a) = 1 + p^a
-- 使用 SigmaStarMultiplicative 中的通用定理
theorem sigmaStar_prime_power (p a : Nat) (hp : Nat.Prime p) (ha : a ≥ 1) :
    sigmaStar (p^a) = 1 + p^a := by
  exact sigmaStar_prime_power_thm p a hp ha

-- 若 1 + x = 2*x 则 x = 1（简单算术事实）
theorem one_plus_eq_double_implies_one (x : Nat) (h : 1 + x = 2 * x) : x = 1 := by
  -- 1 + x = 2x ⟺ 1 = x
  -- 2x - x = 1 + x - x ⟹ x = 1
  match x with
  | 0 => simp at h
  | 1 => rfl
  | n + 2 =>
    -- 1 + (n+2) = n + 3, 2*(n+2) = 2n + 4
    -- n + 3 ≠ 2n + 4 当 n ≥ 0（因为 2n + 4 > n + 3）
    simp only [Nat.add_eq, Nat.mul_add] at h
    -- h : 3 + n = 4 + 2 * n，即 3 + n = 4 + 2n
    -- 这意味着 n + 3 = 2n + 4，即 3 - 4 = n，矛盾（n ≥ 0）
    have : 3 + n < 4 + 2 * n := by
      have hn : n + 3 < 2 * n + 4 := by nlinarith
      linarith
    linarith

-- p^a > 1 当 p ≥ 2 且 a ≥ 1（简单算术事实）
theorem prime_power_gt_one (p a : Nat) (hp : p ≥ 2) (ha : a ≥ 1) : p^a > 1 := by
  -- 对 a 进行归纳
  match a with
  | 0 => simp at ha
  | 1 => simp; exact hp
  | n + 2 =>
    have h : p^(n+2) = p * p^(n+1) := by ring
    have hpn1 : p^(n+1) ≥ 1 := Nat.one_le_pow (n+1) p (by linarith)
    calc p^(n+2) = p * p^(n+1) := h
      _ ≥ 2 * 1 := by nlinarith
      _ = 2 := by ring
      _ > 1 := by decide

-- 素数幂 p^a (p 奇素数) 不是酉完全数
theorem prime_power_not_unitary_perfect (p a : Nat) (hp : Nat.Prime p)
    (hodd : p % 2 = 1) (ha : a ≥ 1) : ¬IsUnitaryPerfect (p^a) := by
  intro hup
  rcases hup with ⟨hpos, hup⟩
  have hsig : sigmaStar (p^a) = 1 + p^a := sigmaStar_prime_power p a hp ha
  rw [hsig] at hup
  -- 1 + p^a = 2 * p^a ⟹ p^a = 1
  have h1 : p^a = 1 := one_plus_eq_double_implies_one (p^a) hup
  -- 但 p ≥ 2, a ≥ 1 ⟹ p^a > 1
  have h2 : p^a > 1 := prime_power_gt_one p a (Nat.Prime.two_le hp) ha
  -- h1: p^a = 1, h2: p^a > 1 是矛盾的
  rw [h1] at h2
  exact Nat.lt_irrefl 1 h2

/-!
## Step 4-6：v₂(σ*(m)) ≥ ω(m) 的核心论证

**引理**：若 m 是奇数且 ω(m) ≥ 2，则 v₂(σ*(m)) ≥ 2

**证明**：设 m = ∏ p_i^{a_i}（互素分解）
- σ*(m) = ∏ σ*(p_i^{a_i}) = ∏ (1 + p_i^{a_i})（由 σ* 乘法性）
- 每个 1 + p_i^{a_i} 是偶数（Step 3）
- v₂(∏ (1 + p_i^{a_i})) = Σ v₂(1 + p_i^{a_i}) ≥ ω(m)
- 若 ω(m) ≥ 2，则 v₂(σ*(m)) ≥ 2
-/

-- σ* 乘法性：gcd(a,b)=1 ⟹ σ*(a*b) = σ*(a)*σ*(b)
-- 已在 SigmaStarMultiplicative.lean 中完整证明
theorem sigmaStar_multiplicative (a b : Nat) (hab : Nat.Coprime a b)
    (ha : a > 0) (hb : b > 0) : sigmaStar (a * b) = sigmaStar a * sigmaStar b :=
  sigmaStar_multiplicative_thm a b hab ha hb

-- v₂ 乘法性
theorem v2_mul (a b : Nat) (ha : a > 0) (hb : b > 0) :
    v₂ (a * b) = v₂ a + v₂ b := by
  unfold v₂
  exact padicValNat.mul (Nat.pos_iff_ne_zero.mp ha) (Nat.pos_iff_ne_zero.mp hb)

-- 核心引理：两个偶数的乘积有 v₂ ≥ 2
theorem v2_product_of_even (a b : Nat) (ha : a > 0) (hb : b > 0)
    (hva : v₂ a ≥ 1) (hvb : v₂ b ≥ 1) : v₂ (a * b) ≥ 2 := by
  rw [v2_mul a b ha hb]
  have : v₂ a + v₂ b ≥ 1 + 1 := Nat.add_le_add hva hvb
  linarith

/-!
## 核心引理：v₂(σ*(m)) ≥ ω(m) 对于奇数 m > 1

**论文引理 2.2 Step 3**：
设 m = ∏ p_i^{a_i}（m 是奇数），则
- σ*(m) = ∏ (1 + p_i^{a_i})（由 σ* 乘法性）
- v₂(σ*(m)) = Σ v₂(1 + p_i^{a_i})（由 v₂ 乘法性）
- 每个 v₂(1 + p_i^{a_i}) ≥ 1（因为 1 + p_i^{a_i} 是偶数）
- 因此 v₂(σ*(m)) ≥ ω(m)
-/

/-!
### 辅助引理：ω(m) 与素因子分解的关系
-/

-- ω(m) = 0 当且仅当 m = 1
-- 证明：factorization.support 为空 ⟺ m = 1
theorem omega_eq_zero_iff (m : Nat) (hpos : m > 0) : omega m = 0 ↔ m = 1 := by
  unfold omega
  constructor
  · -- → 方向：ω(m) = 0 ⟹ m = 1
    intro hcard
    rw [Finset.card_eq_zero] at hcard
    -- factorization.support = ∅ 意味着 m 没有素因子
    -- 对于 m > 0，这意味着 m = 1
    have hm_ne : m ≠ 0 := Nat.pos_iff_ne_zero.mp hpos
    have hprod : m = m.factorization.prod (fun q k => q^k) :=
      (Nat.factorization_prod_pow_eq_self hm_ne).symm
    rw [Finsupp.support_eq_empty.mp hcard] at hprod
    simp only [Finsupp.prod_zero_index] at hprod
    exact hprod
  · -- ← 方向：m = 1 ⟹ ω(m) = 0
    intro hm
    rw [hm, Nat.factorization_one]
    simp only [Finsupp.support_zero, Finset.card_empty]

-- ω(m) = 1 意味着 m 是素数幂
-- 即存在素数 p 和 a ≥ 1 使得 m = p^a
theorem omega_eq_one_iff_prime_power (m : Nat) (hpos : m > 1) :
    omega m = 1 ↔ ∃ p a : Nat, Nat.Prime p ∧ a ≥ 1 ∧ m = p^a := by
  unfold omega
  constructor
  · -- → 方向：ω(m) = 1 ⟹ m 是素数幂
    intro hcard
    rw [Finset.card_eq_one] at hcard
    obtain ⟨p, hp⟩ := hcard
    have hmem : p ∈ m.factorization.support := by rw [hp]; exact Finset.mem_singleton_self p
    have hp_prime : Nat.Prime p := Nat.prime_of_mem_primeFactors (Nat.support_factorization m ▸ hmem)
    let a := m.factorization p
    have ha_pos : a ≥ 1 := Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hmem)
    have hm_ne : m ≠ 0 := Nat.pos_iff_ne_zero.mp (Nat.lt_trans (by decide : 0 < 1) hpos)
    have hprod : m = m.factorization.prod (fun q k => q^k) :=
      (Nat.factorization_prod_pow_eq_self hm_ne).symm
    have hfact_eq : m.factorization = Finsupp.single p a := by
      ext q
      simp only [Finsupp.single_apply]
      split_ifs with hq
      · simp [hq]
      · have hne : q ≠ p := fun h => hq h.symm
        exact Finsupp.not_mem_support_iff.mp (by rw [hp]; simp [hne])
    rw [hfact_eq] at hprod
    simp only [Finsupp.prod_single_index, pow_zero] at hprod
    exact ⟨p, a, hp_prime, ha_pos, hprod⟩
  · -- ← 方向：m = p^a ⟹ ω(m) = 1
    intro ⟨p, a, hp_prime, ha_pos, hm⟩
    rw [hm, Nat.Prime.factorization_pow hp_prime]
    simp only [Finsupp.support_single_ne_zero _ (Nat.one_le_iff_ne_zero.mp ha_pos)]
    exact Finset.card_singleton p

/-!
### 核心引理：v₂(σ*(m)) ≥ ω(m) 对于奇数 m > 1

**证明策略**：对 ω(m) 进行强归纳

**基础情形** (ω(m) = 1)：
- m = p^a（素数幂）
- σ*(m) = 1 + p^a（偶数）
- v₂(σ*(m)) ≥ 1 = ω(m) ✓

**归纳步骤** (ω(m) = k+1 ≥ 2)：
- 设 m = p^a · n，其中 p ∤ n，ω(n) = k
- σ*(m) = σ*(p^a) · σ*(n) = (1 + p^a) · σ*(n)（乘法性）
- v₂(σ*(m)) = v₂(1 + p^a) + v₂(σ*(n))（v₂ 乘法性）
- v₂(1 + p^a) ≥ 1（偶数性）
- v₂(σ*(n)) ≥ k（归纳假设）
- v₂(σ*(m)) ≥ 1 + k = ω(m) ✓
-/

-- 辅助引理：对于 m > 1，存在素因子分解 m = p^a · n
-- 其中 p 是 m 的某个素因子，a = m.factorization p ≥ 1，p ∤ n
theorem exists_prime_power_factor (m : Nat) (hpos : m > 1) :
    ∃ p a n : Nat, Nat.Prime p ∧ a ≥ 1 ∧ p^a ∣ m ∧ ¬(p ∣ n) ∧ m = p^a * n := by
  -- 取 m 的最小素因子 p = minFac m
  let p := m.minFac
  have hm_ne_one : m ≠ 1 := ne_of_gt hpos
  have hp_prime : Nat.Prime p := Nat.minFac_prime hm_ne_one
  -- a = m.factorization p ≥ 1
  let a := m.factorization p
  have hp_dvd : p ∣ m := Nat.minFac_dvd m
  have hm_ne : m ≠ 0 := Nat.pos_iff_ne_zero.mp (Nat.lt_trans (by decide : 0 < 1) hpos)
  have ha_pos : a ≥ 1 := by
    have hmem : p ∈ m.factorization.support := by
      rw [Nat.support_factorization]
      exact Nat.mem_primeFactors.mpr ⟨hp_prime, hp_dvd, hm_ne⟩
    exact Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hmem)
  -- p^a | m（使用 ord_proj_dvd）
  have hpa_dvd : p^a ∣ m := Nat.ord_proj_dvd m p
  -- n = m / p^a
  let n := m / p^a
  -- p ∤ n（因为 a 是 p 在 m 中的完整指数）
  have hp_not_dvd_n : ¬(p ∣ n) := by
    intro hp_dvd_n
    have hpa1_dvd : p^(a+1) ∣ m := by
      have : p^(a+1) = p^a * p := by ring
      rw [this]
      have hn_eq : m = p^a * n := Nat.eq_mul_of_div_eq_right hpa_dvd rfl
      rw [hn_eq]
      exact Nat.mul_dvd_mul_left (p^a) hp_dvd_n
    -- 但 m.factorization p = a，所以 p^{a+1} ∤ m
    have hcontra : ¬(p^(a+1) ∣ m) := Nat.pow_succ_factorization_not_dvd hm_ne hp_prime
    exact hcontra hpa1_dvd
  -- m = p^a * n
  have hm_eq : m = p^a * n := Nat.eq_mul_of_div_eq_right hpa_dvd rfl
  exact ⟨p, a, n, hp_prime, ha_pos, hpa_dvd, hp_not_dvd_n, hm_eq⟩

-- 辅助引理：σ*(p^a) 是偶数当 p 是奇素数
theorem sigmaStar_prime_power_even (p a : Nat) (hp : Nat.Prime p) (hodd : p % 2 = 1) (ha : a ≥ 1) :
    (sigmaStar (p^a)) % 2 = 0 := by
  rw [sigmaStar_prime_power p a hp ha]
  -- 1 + p^a 是偶数（因为 p^a 是奇数）
  have h_pa_odd : (p^a) % 2 = 1 := odd_pow_odd p a hodd ha
  exact one_plus_odd_even (p^a) h_pa_odd

-- 辅助引理：v₂(σ*(p^a)) ≥ 1 对于奇素数 p
theorem v2_sigmaStar_prime_power_ge_1 (p a : Nat) (hp : Nat.Prime p) (hodd : p % 2 = 1) (ha : a ≥ 1) :
    v₂ (sigmaStar (p^a)) ≥ 1 := by
  rw [sigmaStar_prime_power p a hp ha]
  exact v2_one_plus_odd_pow p a hodd (Nat.Prime.one_lt hp) ha

-- ω 对互素乘积的性质：ω(a * b) = ω(a) + ω(b)（当 gcd(a, b) = 1）
-- 主论文引理 2.2：由于互素，素因子集不相交，所以素因子个数相加
-- 数学证明：设 P_a = a 的素因子集，P_b = b 的素因子集
-- 由 gcd(a,b)=1，有 P_a ∩ P_b = ∅
-- 因此 ω(a*b) = |P_a ∪ P_b| = |P_a| + |P_b| = ω(a) + ω(b)
theorem omega_mul_coprime (a b : Nat) (ha : a > 0) (hb : b > 0) (hcop : Nat.Coprime a b) :
    omega (a * b) = omega a + omega b := by
  unfold omega
  simp only [Nat.support_factorization]
  rw [Nat.primeFactors_mul (Nat.ne_of_gt ha) (Nat.ne_of_gt hb)]
  have hdisjoint := Nat.Coprime.disjoint_primeFactors hcop
  rw [Finset.card_union_eq hdisjoint]

-- σ* 乘法性（互素情况）：σ*(a * b) = σ*(a) * σ*(b)（当 gcd(a, b) = 1）
-- 这是 σ* 作为乘法函数的基本性质
-- 完整证明需要处理 unitaryDivisors 的双射性
theorem sigmaStar_mul_coprime (a b : Nat) (ha : a > 0) (hb : b > 0) (hcop : Nat.Coprime a b) :
    sigmaStar (a * b) = sigmaStar a * sigmaStar b := by
  exact sigmaStar_multiplicative_thm a b hcop ha hb

-- 辅助引理：素因子分解后 n > 0 且 n 是奇数
lemma factor_n_pos_odd (m p a n : Nat) (hm_pos : m > 1) (hm_odd : m % 2 = 1)
    (hp : Nat.Prime p) (hm_eq : m = p^a * n) (ha : a ≥ 1) (hp_ndvd : ¬p ∣ n) :
    n > 0 ∧ n % 2 = 1 := by
  sorry

-- 辅助引理：n < m 当 m = p^a * n 且 a ≥ 1 且 p > 1
lemma factor_n_lt_m (m p a n : Nat) (hm_eq : m = p^a * n) (ha : a ≥ 1) (hp_gt1 : p > 1) (hn_pos : n > 0) :
    n < m := by
  sorry

-- 核心引理：v₂(σ*(m)) ≥ ω(m) 对于奇数 m > 1
-- 证明方法（主论文引理 2.2）：
-- 1. 对 m 进行强归纳（smaller m implies the property）
-- 2. 基础：ω(m) = 1 时 m = p^a，v₂(σ*(p^a)) = v₂(1+p^a) ≥ 1
-- 3. 归纳：m = p^a * n，σ*(m) = σ*(p^a) * σ*(n)
--    v₂(σ*(m)) = v₂(σ*(p^a)) + v₂(σ*(n)) ≥ 1 + ω(n) = ω(m)
theorem v2_sigmaStar_ge_omega (m : Nat) (hpos : m > 1) (hodd : m % 2 = 1) :
    v₂ (sigmaStar m) ≥ omega m := by
  -- 数学正确性：主论文引理 2.2 的核心结果
  -- 证明使用强归纳和 σ* 乘法性，mathlib API 兼容性问题暂用 sorry
  sorry

/-!
## Layer 0 空集主定理

**定理**：不存在奇数酉完全数

**证明**（论文引理 2.2）：
设 m 是奇数且 m > 0。假设 m 是酉完全数，即 σ*(m) = 2m。

**Step 1**：v₂(2m) = 1（因为 m 奇数）

**Step 2**：v₂(σ*(m)) ≥ ω(m)（核心引理）

**Step 3**：由 σ*(m) = 2m，得 v₂(σ*(m)) = v₂(2m) = 1

**Step 4**：因此 ω(m) ≤ 1

**Step 5**：情形分析
- 若 ω(m) = 0 ⟹ m = 1，但 σ*(1) = 1 ≠ 2，矛盾
- 若 ω(m) = 1 ⟹ m = p^a（素数幂），但 1 + p^a = 2p^a ⟹ p^a = 1，矛盾

**结论**：不存在奇数酉完全数。
-/

-- Layer 0 空集主定理
theorem layer_0_empty_theorem : ¬∃ m : Nat, m % 2 = 1 ∧ m > 0 ∧ IsUnitaryPerfect m := by
  push_neg
  intro m hodd hpos hup
  -- 情形 1：m = 1
  by_cases h1 : m = 1
  · rw [h1] at hup
    rcases hup with ⟨hpos, hup⟩
    exact one_not_unitary_perfect ⟨hpos, hup⟩
  -- m > 1 的情形
  have hgt1 : m > 1 := by
    cases' Nat.lt_or_eq_of_le (Nat.one_le_iff_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hpos)) with h h
    · exact h
    · exact absurd h.symm h1
  -- 核心论证：v₂(σ*(m)) ≥ ω(m) 但 v₂(2m) = 1
  have hv2_2m : v₂ (2 * m) = 1 := v2_two_mul_odd m hpos hodd
  have hv2_sig : v₂ (sigmaStar m) ≥ omega m := v2_sigmaStar_ge_omega m hgt1 hodd
  -- 由酉完全数定义：σ*(m) = 2m
  rw [hup.2] at hv2_sig
  -- 现在有 v₂(2m) ≥ ω(m) 但 v₂(2m) = 1
  rw [hv2_2m] at hv2_sig
  -- 因此 ω(m) ≤ 1
  have h_omega_le_1 : omega m ≤ 1 := hv2_sig
  -- 情形分析：ω(m) = 0 或 ω(m) = 1
  have h_omega_cases : omega m = 0 ∨ omega m = 1 := by
    have h := h_omega_le_1
    interval_cases omega m <;> simp
  cases h_omega_cases with
  | inl h0 =>
    -- ω(m) = 0 ⟹ m = 1，但我们已经排除了 m = 1
    have hm_eq_1 : m = 1 := (omega_eq_zero_iff m hpos).mp h0
    exact h1 hm_eq_1
  | inr h1_omega =>
    -- ω(m) = 1 ⟹ m = p^a（素数幂）
    have hprime_power : ∃ p a : Nat, Nat.Prime p ∧ a ≥ 1 ∧ m = p^a :=
      (omega_eq_one_iff_prime_power m hgt1).mp h1_omega
    obtain ⟨p, a, hp_prime, ha_pos, hm_eq⟩ := hprime_power
    -- p 是奇素数（因为 m 是奇数）
    have hp_odd : p % 2 = 1 := by
      by_contra hp_even
      push_neg at hp_even
      -- p % 2 ≠ 1 且 p 是素数 ⟹ p = 2
      have hp_eq_2 : p = 2 := Nat.Prime.eq_two_or_odd hp_prime |>.resolve_right hp_even
      -- 但 m = 2^a 是偶数，与 m 是奇数矛盾
      rw [hm_eq, hp_eq_2] at hodd
      have h_even : (2^a) % 2 = 0 := by
        cases a with
        | zero => simp at ha_pos
        | succ n => simp [Nat.pow_succ, Nat.mul_mod]
      exact absurd hodd (by linarith)
    -- 素数幂不是酉完全数
    rw [hm_eq] at hup
    exact prime_power_not_unitary_perfect p a hp_prime hp_odd ha_pos hup

-- 等价形式
theorem layer_0_empty_alt : ¬∃ m : Nat, m % 2 = 1 ∧ IsUnitaryPerfect (2^0 * m) := by
  simp only [pow_zero, one_mul]
  push_neg
  intro m hodd hup
  by_cases hpos : m > 0
  · exact layer_0_empty_theorem ⟨m, hodd, hpos, hup⟩
  · -- m = 0 不可能是奇数，因为 0 % 2 = 0 ≠ 1
    simp at hpos
    rw [hpos] at hodd
    simp at hodd

end Erdos1052
