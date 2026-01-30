"""
Π值与σ*函数计算
"""
from typing import Dict, Tuple, List
from fractions import Fraction
from .factorizations import factor, v2


def sigma_star(n: int) -> int:
    """
    计算酉因子和 σ*(n) = Π(p^a + 1) for p^a || n
    """
    factors = factor(n)
    result = 1
    for p, a in factors.items():
        result *= (p ** a + 1)
    return result


def pi_value(n: int) -> Fraction:
    """
    计算 Π(n) = σ*(n) / n （精确分数形式）
    """
    if n <= 0:
        raise ValueError("n must be positive")
    return Fraction(sigma_star(n), n)


def pi_from_factors(factors: Dict[int, int]) -> Fraction:
    """
    从素因子分解计算 Π 值
    Π(m) = Π_{p^a||m} (p^a + 1) / p^a
    """
    result = Fraction(1, 1)
    for p, a in factors.items():
        pa = p ** a
        result *= Fraction(pa + 1, pa)
    return result


def rho_b(b: int) -> Fraction:
    """
    计算目标值 ρ_b = 2^(b+1) / (2^b + 1)
    """
    numerator = 1 << (b + 1)  # 2^(b+1)
    denominator = (1 << b) + 1  # 2^b + 1
    return Fraction(numerator, denominator)


def is_unitary_perfect(n: int) -> bool:
    """
    判断n是否为酉完全数：σ*(n) = 2n
    """
    return sigma_star(n) == 2 * n


# 已知的5个酉完全数
KNOWN_UNITARY_PERFECT = [
    6,      # 2·3
    60,     # 2^2·3·5
    90,     # 2·3^2·5
    87360,  # 2^6·3·5·7·13
    # n_5 的奇部
]

# n_5 的精确值
N5_ODD_PART = 3 * (5**4) * 7 * 11 * 13 * 19 * 37 * 79 * 109 * 157 * 313
N5 = (1 << 18) * N5_ODD_PART  # 2^18 * m_5


def verify_known_unitary_perfect() -> List[Tuple[int, bool, Dict]]:
    """
    验证已知酉完全数
    """
    all_ups = KNOWN_UNITARY_PERFECT + [N5]
    results = []
    
    for n in all_ups:
        is_up = is_unitary_perfect(n)
        factors = factor(n)
        sigma = sigma_star(n)
        
        info = {
            'n': n,
            'factors': factors,
            'sigma_star': sigma,
            '2n': 2 * n,
            'is_unitary_perfect': is_up
        }
        results.append((n, is_up, info))
    
    return results


def verify_rho_equation(b: int, m: int) -> Dict:
    """
    验证 Π(m) = ρ_b
    """
    pi_m = pi_value(m)
    rho = rho_b(b)
    
    return {
        'b': b,
        'm': m,
        'Pi(m)': pi_m,
        'rho_b': rho,
        'match': pi_m == rho,
        'v2_sigma': v2(sigma_star(m)),
        'target_v2': b + 1
    }


def compute_P_k(k: int) -> Fraction:
    """
    计算 P_k = Π(n) 对前k个奇素数的乘积
    P_k = Π_{i=1}^{k} (p_i + 1) / p_i
    """
    odd_primes = [3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47]
    
    if k > len(odd_primes):
        raise ValueError(f"Only have {len(odd_primes)} primes precomputed")
    
    result = Fraction(1, 1)
    for i in range(k):
        p = odd_primes[i]
        result *= Fraction(p + 1, p)
    
    return result


def verify_P_k_bounds() -> List[Tuple[int, Fraction, float]]:
    """
    验证论文中的P_k值
    """
    results = []
    for k in range(1, 11):
        P_k = compute_P_k(k)
        results.append((k, P_k, float(P_k)))
    return results


if __name__ == "__main__":
    print("=" * 60)
    print("Π值与酉完全数验证")
    print("=" * 60)
    
    print("\n1. 验证已知酉完全数:")
    for n, is_up, info in verify_known_unitary_perfect():
        status = "✓" if is_up else "✗"
        print(f"  [{status}] n = {n}")
        print(f"      σ*(n) = {info['sigma_star']}, 2n = {info['2n']}")
    
    print("\n2. 验证P_k值:")
    for k, P_k, P_k_float in verify_P_k_bounds():
        print(f"  P_{k} = {P_k} ≈ {P_k_float:.6f}")
    
    print("\n3. 验证ρ_b值:")
    for b in [1, 2, 6, 18]:
        rho = rho_b(b)
        print(f"  ρ_{b} = {rho} ≈ {float(rho):.6f}")
    
    print("\n4. 验证n_5的Π方程:")
    m_5 = N5_ODD_PART
    result = verify_rho_equation(18, m_5)
    status = "✓" if result['match'] else "✗"
    print(f"  [{status}] Π(m_5) = ρ_18")
    print(f"      Π(m_5) = {result['Pi(m)']}")
    print(f"      ρ_18   = {result['rho_b']}")
    print(f"      v₂(σ*(m_5)) = {result['v2_sigma']} (目标: {result['target_v2']})")
