"""
吸收闭包计算与v₂贡献分析
"""
from typing import Set, Dict, List, Tuple
from .factorizations import factor, v2, is_prime


def odd_prime_factors(n: int) -> Set[int]:
    """
    返回n的所有奇素因子
    """
    factors = factor(n)
    return {p for p in factors.keys() if p > 2}


def absorption_step(primes: Set[int]) -> Set[int]:
    """
    一步吸收：对于每个素数p，计算p+1的奇素因子
    返回所有新发现的素数
    """
    new_primes = set()
    for p in primes:
        # p + 1 的奇素因子
        new_primes.update(odd_prime_factors(p + 1))
    return new_primes


def absorption_closure(initial_primes: Set[int], max_iterations: int = 100) -> Set[int]:
    """
    计算吸收闭包：从初始素因子集合出发，
    迭代添加所有 (p+1) 的奇素因子，直到闭包稳定
    
    定义：若 p ∈ 闭包，则 (p+1) 的所有奇素因子也在闭包中
    """
    closure = set(initial_primes)
    
    for i in range(max_iterations):
        # 对闭包中每个素数p，计算p+1的奇素因子
        new_from_p_plus_1 = set()
        for p in closure:
            new_from_p_plus_1.update(odd_prime_factors(p + 1))
        
        # 检查是否有新素因子
        new_primes = new_from_p_plus_1 - closure
        if not new_primes:
            break
        
        closure.update(new_primes)
    
    return closure


def extended_absorption_closure(initial_primes: Set[int], max_exponent: int = 4) -> Set[int]:
    """
    扩展吸收闭包：考虑 p^a + 1 (a >= 1) 的奇素因子
    用于L₁₈唯一性分析
    """
    closure = set(initial_primes)
    
    for _ in range(100):  # 最多100次迭代
        new_primes = set()
        
        for p in list(closure):
            for a in range(1, max_exponent + 1):
                pa_plus_1 = p ** a + 1
                new_primes.update(odd_prime_factors(pa_plus_1))
        
        if new_primes <= closure:
            break
        
        closure.update(new_primes)
    
    return closure


def v2_contribution(primes_with_exponents: Dict[int, int]) -> int:
    """
    计算素因子集合对σ*(m)的v₂贡献
    
    v₂(σ*(m)) = Σ v₂(p^a + 1) for p^a || m
    """
    total = 0
    for p, a in primes_with_exponents.items():
        total += v2(p ** a + 1)
    return total


def v2_max_from_closure(closure: Set[int]) -> Tuple[int, Dict[int, int]]:
    """
    计算吸收闭包能达到的最大v₂贡献
    假设每个素因子指数为1
    
    返回 (最大v₂, 各素数的v₂贡献)
    """
    contributions = {}
    for p in closure:
        contributions[p] = v2(p + 1)
    
    return sum(contributions.values()), contributions


def compute_core_b(b: int) -> Tuple[int, Dict[int, int], Set[int]]:
    """
    计算层Lb的核心(Core_b)及其吸收闭包
    
    Core_b = 2^b + 1 的素因子集合
    返回：(2^b+1, 分解, 吸收闭包)
    """
    n = (1 << b) + 1
    factors = factor(n)
    core_primes = set(factors.keys())
    
    closure = absorption_closure(core_primes)
    
    return n, factors, closure


def verify_absorption_closure_for_b(b: int) -> Dict:
    """
    验证特定b值的吸收闭包计算
    """
    n, factors, closure = compute_core_b(b)
    
    # 计算v₂贡献
    v2_core = v2_contribution(factors)
    v2_max, v2_details = v2_max_from_closure(closure)
    
    result = {
        'b': b,
        '2^b+1': n,
        'core_factors': factors,
        'closure': sorted(closure),
        'closure_size': len(closure),
        'v2_core': v2_core,
        'v2_max_closure': v2_max,
        'v2_target': b + 1,
        'v2_gap': (b + 1) - v2_max,
        'reachable': v2_max >= b + 1
    }
    
    return result


def verify_all_absorptions(max_b: int = 30) -> List[Dict]:
    """
    验证b=1到max_b的所有吸收闭包
    """
    results = []
    for b in range(1, max_b + 1):
        results.append(verify_absorption_closure_for_b(b))
    return results


if __name__ == "__main__":
    print("=" * 70)
    print("吸收闭包与v₂贡献验证")
    print("=" * 70)
    
    for b in [1, 2, 6, 18, 19, 20, 25, 30]:
        result = verify_absorption_closure_for_b(b)
        
        status = "✓ 可达" if result['reachable'] else "✗ 不可达"
        print(f"\nb = {b}:")
        print(f"  2^b+1 = {result['2^b+1']}")
        print(f"  Core = {result['core_factors']}")
        print(f"  闭包大小 = {result['closure_size']}")
        print(f"  v₂(Core) = {result['v2_core']}")
        print(f"  v₂(闭包最大) = {result['v2_max_closure']}")
        print(f"  目标v₂ = {result['v2_target']}")
        print(f"  状态: {status} (缺口={result['v2_gap']})")
    
    print("\n" + "=" * 70)
    print("高层(b≥19)的v₂不可达性验证")
    print("=" * 70)
    
    all_unreachable = True
    for b in range(19, 31):
        result = verify_absorption_closure_for_b(b)
        if result['reachable']:
            print(f"  警告: b={b} 可能可达!")
            all_unreachable = False
    
    if all_unreachable:
        print("  ✓ 所有b∈[19,30]均不可达（基于闭包指数=1假设）")
