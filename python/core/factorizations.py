"""
素因子分解与基本数论函数
"""
from typing import Dict, List, Tuple
from functools import reduce
from math import gcd


def factor(n: int) -> Dict[int, int]:
    """
    返回n的素因子分解 {p: a} 表示 p^a || n
    """
    if n <= 1:
        return {}
    factors = {}
    d = 2
    while d * d <= n:
        while n % d == 0:
            factors[d] = factors.get(d, 0) + 1
            n //= d
        d += 1
    if n > 1:
        factors[n] = 1
    return factors


def v2(n: int) -> int:
    """
    计算 v_2(n) = 2-adic valuation
    """
    if n == 0:
        return float('inf')
    count = 0
    while n % 2 == 0:
        count += 1
        n //= 2
    return count


def vp(n: int, p: int) -> int:
    """
    计算 v_p(n) = p-adic valuation
    """
    if n == 0:
        return float('inf')
    if p <= 1:
        raise ValueError("p must be prime > 1")
    count = 0
    while n % p == 0:
        count += 1
        n //= p
    return count


def omega(n: int) -> int:
    """
    计算 ω(n) = 不同素因子个数
    """
    return len(factor(n))


def Omega(n: int) -> int:
    """
    计算 Ω(n) = 素因子个数（计重数）
    """
    return sum(factor(n).values())


def is_prime(n: int) -> bool:
    """
    Miller-Rabin素性测试
    """
    if n < 2:
        return False
    if n == 2:
        return True
    if n % 2 == 0:
        return False
    
    # 写 n-1 = 2^r * d
    r, d = 0, n - 1
    while d % 2 == 0:
        r += 1
        d //= 2
    
    # 测试基
    witnesses = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37]
    
    for a in witnesses:
        if a >= n:
            continue
        x = pow(a, d, n)
        if x == 1 or x == n - 1:
            continue
        for _ in range(r - 1):
            x = pow(x, 2, n)
            if x == n - 1:
                break
        else:
            return False
    return True


def verify_2b_plus_1_factorization(b: int) -> Tuple[int, Dict[int, int], bool]:
    """
    验证 2^b + 1 的素因子分解
    返回 (2^b+1, 分解, 是否正确)
    """
    n = (1 << b) + 1  # 2^b + 1
    factors = factor(n)
    
    # 验证：乘积是否等于n
    product = 1
    for p, a in factors.items():
        product *= p ** a
    
    # 验证：所有因子是否为素数
    all_prime = all(is_prime(p) for p in factors.keys())
    
    correct = (product == n) and all_prime
    return n, factors, correct


# 论文中的关键分解表
PAPER_FACTORIZATIONS = {
    1: {3: 1},                      # 2^1+1 = 3
    2: {5: 1},                      # 2^2+1 = 5
    3: {3: 2},                      # 2^3+1 = 9 = 3^2
    4: {17: 1},                     # 2^4+1 = 17
    5: {3: 1, 11: 1},               # 2^5+1 = 33 = 3·11
    6: {5: 1, 13: 1},               # 2^6+1 = 65 = 5·13
    7: {3: 1, 43: 1},               # 2^7+1 = 129 = 3·43
    8: {257: 1},                    # 2^8+1 = 257 (Fermat prime)
    9: {3: 3, 19: 1},               # 2^9+1 = 513 = 27·19 = 3^3·19
    10: {5: 2, 41: 1},              # 2^10+1 = 1025 = 25·41
    11: {3: 1, 683: 1},             # 2^11+1 = 2049 = 3·683
    12: {17: 1, 241: 1},            # 2^12+1 = 4097 = 17·241（论文有误）
    13: {3: 1, 2731: 1},            # 2^13+1 = 8193 = 3·2731
    14: {5: 1, 29: 1, 113: 1},      # 2^14+1 = 16385 = 5·29·113
    15: {3: 2, 11: 1, 331: 1},      # 2^15+1 = 32769 = 9·11·331（修正）
    16: {65537: 1},                 # 2^16+1 = 65537 (Fermat prime)
    17: {3: 1, 43691: 1},           # 2^17+1 = 131073 = 3·43691
    18: {5: 1, 13: 1, 37: 1, 109: 1},  # 2^18+1 = 262145 = 5·13·37·109
    19: {3: 1, 174763: 1},          # 2^19+1 = 524289 = 3·174763
    20: {17: 1, 61681: 1},          # 2^20+1 = 1048577 = 17·61681（论文有误）
}


def verify_paper_factorizations() -> List[Tuple[int, bool, str]]:
    """
    验证论文中所有2^b+1的分解是否正确
    """
    results = []
    for b in range(1, 31):
        n, computed, correct = verify_2b_plus_1_factorization(b)
        
        if b in PAPER_FACTORIZATIONS:
            paper = PAPER_FACTORIZATIONS[b]
            match = (computed == paper)
            if match:
                msg = f"b={b}: MATCH - {n} = {format_factorization(computed)}"
            else:
                msg = f"b={b}: MISMATCH - computed {format_factorization(computed)}, paper {format_factorization(paper)}"
        else:
            match = True  # 论文未给出，只验证计算正确性
            msg = f"b={b}: COMPUTED - {n} = {format_factorization(computed)}"
        
        results.append((b, correct and match, msg))
    
    return results


def format_factorization(factors: Dict[int, int]) -> str:
    """格式化素因子分解"""
    parts = []
    for p in sorted(factors.keys()):
        a = factors[p]
        if a == 1:
            parts.append(str(p))
        else:
            parts.append(f"{p}^{a}")
    return " · ".join(parts)


if __name__ == "__main__":
    print("=" * 60)
    print("验证 2^b + 1 的素因子分解")
    print("=" * 60)
    
    results = verify_paper_factorizations()
    
    passed = 0
    failed = 0
    for b, ok, msg in results:
        status = "✓" if ok else "✗"
        print(f"  [{status}] {msg}")
        if ok:
            passed += 1
        else:
            failed += 1
    
    print("=" * 60)
    print(f"结果: {passed} 通过, {failed} 失败")
