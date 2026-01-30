# Erdős Problem #1052 代码证明

## 验证架构

```
代码证明/
├── python/                    # 数值验证层
│   ├── verify_all.py          # 主验证入口
│   ├── core/                  # 核心验证模块
│   │   ├── factorizations.py  # 2^b+1 分解验证
│   │   ├── absorption.py      # 吸收闭包计算
│   │   ├── v2_sums.py         # v₂ 累加验证
│   │   └── pi_values.py       # Π值计算
│   ├── layers/                # 各层验证
│   │   ├── L1_L2_L6.py        # 非空层验证
│   │   ├── L3_L17.py          # 中间层排除
│   │   └── L18_uniqueness.py  # L₁₈唯一性
│   └── bounds/                # 上界验证
│       └── robin_bounds.py    # Robin上界验证
│
└── lean/                      # 形式化证明层
    ├── Erdos1052.lean         # 主定理
    ├── Basic.lean             # 基础定义
    ├── UnitaryDivisor.lean    # 酉因子理论
    ├── Absorption.lean        # 吸收闭包
    └── L18Unique.lean         # L₁₈唯一性
```

## 两层验证的角色

### Python层：验证"是什么"
- 验证论文中所有具体数值计算
- 发现潜在的算术错误
- 生成Lean需要的具体实例

### Lean层：证明"为什么"
- 形式化核心定理的逻辑结构
- 机器验证每一步推理
- 提供不可挑战的严格性

## 严格性保证

| 层次 | 保证内容 | 可能出错的地方 |
|------|----------|----------------|
| Python | 计算正确性 | 代码逻辑bug |
| Lean | 逻辑推理正确性 | 形式化与原问题不一致 |
| 交叉验证 | 两层一致性 | - |

## 运行方式

```bash
# Python验证
cd python
python verify_all.py

# Lean验证
cd lean
lake build
```

## 验证状态

### Python验证模块 (已实现)
- [x] `core/factorizations.py` - 素因子分解、v₂计算、Miller-Rabin素性测试
- [x] `core/absorption.py` - 吸收闭包计算、v₂贡献分析
- [x] `core/pi_values.py` - Π值、σ*函数、ρ_b计算、酉完全数验证
- [x] `layers/L18_uniqueness.py` - L₁₈唯一性完整验证
- [x] `verify_all.py` - 主验证入口
- [x] `test_basic.py` - 基础功能测试

### Lean形式化框架 (已搭建)
- [x] `Erdos1052/Basic.lean` - 基础定义：酉因子、σ*函数、Π函数、ρ_b、层定义
- [x] `Erdos1052/L18Unique.lean` - L₁₈唯一性：核心必要性、链式吸收、v₅平衡、Zsigmondy论证
- [x] `Main.lean` - 主定理：酉完全数有限且恰为5个
- [ ] 填充`sorry`占位符（需要数学工作）

## 运行指南

### Python验证
```bash
cd python
python test_basic.py      # 基础测试
python verify_all.py      # 完整验证
python layers/L18_uniqueness.py  # L₁₈专项验证
```

### Lean验证
```bash
cd lean
lake update    # 首次运行，下载mathlib
lake build     # 构建项目
```

## 严格性说明

### 为什么Python+Lean组合有效？

| 层次 | 工具 | 保证内容 | 局限性 |
|------|------|----------|--------|
| **计算验证** | Python | 所有数值计算正确 | 不证明逻辑 |
| **逻辑验证** | Lean | 推理过程正确 | 需正确形式化 |
| **交叉验证** | 两者对照 | 形式化与问题一致 | - |

### Lean的"绝对严格"是什么意思？

1. **类型检查 = 证明验证**：Lean基于依赖类型理论(Curry-Howard对应)
   - 声明`theorem T : P`意味着构造类型为P的项
   - 类型检查通过 = 证明在数学逻辑上正确

2. **可能出错的地方**：
   - 公理假设错误（使用标准Mathlib避免）
   - 形式化与原问题不一致（Python交叉验证）
   - Lean核心bug（<1万行代码，经过大量审计）

3. **Python的作用**：
   - 验证具体数值实例
   - 确保形式化定义与原问题一致
   - 快速发现潜在错误
