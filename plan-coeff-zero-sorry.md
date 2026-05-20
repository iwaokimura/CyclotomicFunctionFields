# Plan: `coeff_zero_of_not_q_power` の `sorry` を解消する

## Context

`CyclotomicFunctionFields/Carlitz/Additive.lean` の `coeff_zero_of_not_q_power`
（line 179–280）に唯一残っている `sorry` を解消する。

この sorry は `key` というラベルで line 269 にあり、ゴールは：

```
key : coeff_K * (n.choose k : K) = 0
```

ここで
- `K = RatFunc (Fq q)` (無限体、標数 q)
- `coeff_K = algebraMap (Fq q) K (P.coeff n)`
- `0 < k < n`、`n` は q の冪でない
- `(n.choose k : K) ≠ 0` はすでに `binom_ne_zero_K` として証明済み

これが示せれば `coeff_K = 0` → `P.coeff n = 0` と帰結でき、
`structure_theorem` の sorry も unblock される。

---

## 戦略

**二変数多項式 `MvPolynomial (Fin 2) K` を使う。**

### アイデア

`hxy : ∀ x y : K, aeval x P + aeval y P = aeval (x+y) P`

を K 上の二変数多項式の等式にリフトする：

```
P(X₀ + X₁) = P(X₀) + P(X₁)   in  MvPolynomial (Fin 2) K
```

これが成立するのは `MvPolynomial.funext` による（K は無限環）。

その後、モノミアル `m = {0 ↦ k, 1 ↦ (n-k)}` の係数を両辺で比較する：

- **左辺** `P(X₀ + X₁)` の `X₀^k · X₁^(n-k)` 係数：
  二項定理より = `P.coeff n · C(n,k)`

- **右辺** `P(X₀) + P(X₁)` の `X₀^k · X₁^(n-k)` 係数：
  `P(X₀)` は X₀ のみの単項式の和、`P(X₁)` は X₁ のみ。
  `0 < k` かつ `0 < n-k` なので混合項は現れない → `= 0`

よって `P.coeff n · C(n,k) = 0`。`C(n,k) ≠ 0` より `P.coeff n = 0`。

---

## 実装ステップ（`key` ブロック内）

### Step A: 二変数多項式を定義

```lean
let P' : Polynomial K := P.map (algebraMap (Fq q) K)
let lhs_poly : MvPolynomial (Fin 2) K :=
  Polynomial.aeval (MvPolynomial.X 0 + MvPolynomial.X 1) P'
let rhs_poly : MvPolynomial (Fin 2) K :=
  Polynomial.aeval (MvPolynomial.X 0) P' + Polynomial.aeval (MvPolynomial.X 1) P'
```

### Step B: `MvPolynomial.funext` で等式を確立

```lean
have poly_eq : lhs_poly = rhs_poly := by
  apply MvPolynomial.funext
  intro x
  simp only [lhs_poly, rhs_poly, map_add, Polynomial.aeval_def,
             MvPolynomial.eval_add]
  -- hxy を x 0 と x 1 に特殊化
  have h := hxy (x 0) (x 1)
  -- algebraMap の合成を整理して等式を繋げる
  simp [Polynomial.eval₂_map, ← Polynomial.aeval_def] at h ⊢
  linarith  -- または exact h.symm 等
```

### Step C: モノミアルの係数を抽出

```lean
let m : Fin 2 →₀ ℕ := Finsupp.single 0 k + Finsupp.single 1 (n - k)
have coeff_eq := congr_arg (MvPolynomial.coeff m) poly_eq
```

### Step D: 左辺係数の計算（二項定理）

`Polynomial.aeval (X₀ + X₁) P'` の `m` 係数を計算する。

主に使うべき補題：
- `Polynomial.aeval_sum`（P' の各項を展開）
- `MvPolynomial.coeff_X_pow` または `add_pow` の MvPolynomial 版
- `MvPolynomial.coeff_monomial`

期待する結果：
```lean
have lhs_coeff : MvPolynomial.coeff m lhs_poly = coeff_K * (n.choose k : K)
```

### Step E: 右辺係数の計算（= 0）

`P(X₀)` の各モノミアルは `Finsupp.single 0 i` 型（X₀ の i 乗のみ）、
`P(X₁)` は `Finsupp.single 1 i` 型。
`m = Finsupp.single 0 k + Finsupp.single 1 (n-k)` は k > 0 かつ n-k > 0 より混合項なので係数は 0。

```lean
have rhs_coeff : MvPolynomial.coeff m rhs_poly = 0
```

### Step F: 結論

```lean
have : coeff_K * (n.choose k : K) = 0 := by
  rw [← lhs_coeff, ← rhs_coeff, coeff_eq]
exact this
```

---

## 使用する主な Mathlib 補題

| 補題 | 用途 |
|---|---|
| `MvPolynomial.funext` | 無限環上の多変数多項式 pointwise 等式 → 等式 |
| `Polynomial.aeval_map_algebraMap` | `P'.aeval` と `P.aeval` の関係 |
| `Polynomial.aeval_sum` | Σ に対する aeval の分配 |
| `MvPolynomial.coeff_add` | coeff の加法性 |
| `MvPolynomial.coeff_X_pow` | `X i ^ n` の係数 |
| `add_pow` / binomial in MvPolynomial | `(X 0 + X 1)^n` の展開 |
| `Finsupp.single_add` | Finsupp 算術 |

---

## `structure_theorem` の sorry

`coeff_zero_of_not_q_power` が閉じれば、既に証明済みの
`support_subset_q_powers` を経由して：

```lean
theorem structure_theorem (P : Polynomial (Fq q)) (hP : IsAdditive P) :
  ∃ (n : ℕ) (coeffs : ℕ → Fq q),
    P = Finset.sum (Finset.range n) (fun i => coeffs i • frobeniusPower i)
```

を `P.as_sum_support` と `support_subset_q_powers` で構成できる。

---

## 検証方法

1. `lake build CyclotomicFunctionFields.Carlitz.Additive` でエラーなし確認
2. `#check IsAdditive.coeff_zero_of_not_q_power` が sorry なしで通ること
3. `#check IsAdditive.structure_theorem` も同様
4. `lake build` 全体が通ること
