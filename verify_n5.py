# 验证 n5 的值
n5 = 2**18 * 3 * 5**4 * 7 * 11 * 13 * 19 * 37 * 79 * 109 * 157 * 313
m5 = 3 * 5**4 * 7 * 11 * 13 * 19 * 37 * 79 * 109 * 157 * 313
print("n5 =", n5)
print("m5 =", m5)
print("2^18 =", 2**18)

# Basic.lean 中的值
lean_n5 = 146361946186458562560000
lean_m5 = 558326515909036875

print()
print("Lean中定义的n5 =", lean_n5)
print("Lean中定义的m5 =", lean_m5)
print()
print("n5 匹配:", n5 == lean_n5)
print("m5 匹配:", m5 == lean_m5)
