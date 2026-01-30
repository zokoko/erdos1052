"""
基础测试脚本
"""
import sys
import os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

print("=" * 60)
print("Erdos 1052 基础测试")
print("=" * 60)

# 测试1: 素因子分解
print("\n[1] 测试素因子分解...")
from core.factorizations import factor, v2, format_factorization

n = 262145  # 2^18 + 1
factors = factor(n)
print(f"  2^18 + 1 = {n} = {format_factorization(factors)}")
expected = {5: 1, 13: 1, 37: 1, 109: 1}
if factors == expected:
    print("  ✓ 分解正确!")
else:
    print(f"  ✗ 分解错误! 期望: {expected}")

# 测试2: v2计算
print("\n[2] 测试v2计算...")
test_cases = [(4, 2), (8, 3), (12, 2), (20, 2), (80, 4)]
all_ok = True
for n, expected_v2 in test_cases:
    actual = v2(n)
    status = "✓" if actual == expected_v2 else "✗"
    print(f"  [{status}] v2({n}) = {actual} (期望: {expected_v2})")
    if actual != expected_v2:
        all_ok = False

# 测试3: 酉因子和
print("\n[3] 测试酉因子和...")
from core.pi_values import sigma_star

# σ*(6) = (2+1)(3+1) = 12 = 2*6, 所以6是酉完全数
n = 6
sigma = sigma_star(n)
print(f"  σ*({n}) = {sigma}, 2n = {2*n}")
if sigma == 2*n:
    print("  ✓ 6是酉完全数!")
else:
    print("  ✗ 计算错误!")

# 测试4: m5验证
print("\n[4] 测试m5...")
m5 = 3 * (5**4) * 7 * 11 * 13 * 19 * 37 * 79 * 109 * 157 * 313
print(f"  m5 = {m5}")
sigma_m5 = sigma_star(m5)
v2_sigma = v2(sigma_m5)
print(f"  σ*(m5) = {sigma_m5}")
print(f"  v2(σ*(m5)) = {v2_sigma}")
if v2_sigma == 19:
    print("  ✓ v2 = 19 正确!")
else:
    print(f"  ✗ v2 应为19，实际为 {v2_sigma}")

print("\n" + "=" * 60)
print("测试完成")
print("=" * 60)
