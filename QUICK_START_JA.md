# クイックスタートガイド

## プロジェクトの概要

このプロジェトは、Hayes の「有理関数体の明示的類体論」をLean4で形式化することを目的としています。
特に、Carlitz加群の分岐点を用いた巡回函数体の理論に焦点を当てています。

## セットアップ手順

### 1. elanのインストール

```bash
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
elan self update
```

### 2. プロジェクトディレクトリに移動

```bash
cd CyclotomicFunctionFields
```

### 3. mathlibのキャッシュを取得（コンパイル時間を大幅に短縮）

```bash
lake exe cache get
```

### 4. プロジェクトをビルド

```bash
lake build
```

### 5. VS Codeで開く

```bash
code .
```

## プロジェクト構造

```
CyclotomicFunctionFields/
├── README.md                           # プロジェクト概要
├── INSTALL.md                          # 詳細なインストールガイド
├── ROADMAP.md                          # 開発ロードマップ
├── QUICK_START_JA.md                   # このファイル
├── lakefile.toml                       # Lake設定
├── lean-toolchain                      # Leanバージョン
├── CyclotomicFunctionFields.lean      # ルートインポートファイル
└── CyclotomicFunctionFields/
    ├── Prelude.lean                    # 基本設定（Fq, A, K, L）
    ├── Carlitz/
    │   ├── Basic.lean                  # Carlitz加群の定義
    │   ├── Additive.lean               # 加法的多項式
    │   ├── Torsion.lean                # 分岐点 Λ_M
    │   └── Field.lean                  # 巡回函数体 K(Λ_M)
    ├── ClassField/
    │   └── Setup.lean                  # 将来のCFT接続
    └── Examples.lean                   # 明示的な計算例
```

## 主要な概念

### Carlitz加群

Carlitz加群は生成元 t への作用によって定義されます：

φ_t(x) = tx + x^q

ここで x^q はFrobenius写像です。

### 分岐点（torsion points）

M ∈ A に対して、M-分岐点は以下で定義されます：

Λ_M = {x ∈ L : φ_M(x) = 0}

主要な性質：
- |Λ_M| = q^(deg M)
- Λ_M ≅ A/M （A-加群として）
- タワー性質: M | N ⟹ Λ_M ⊆ Λ_N

### Hayesの主定理

K = 𝔽_q(t) の任意の有限アーベル拡大は、ある K(Λ_M) に含まれる。

これは函数体に対するKronecker-Weber定理の類似です。

## 開発ワークフロー

### 日々の開発サイクル

1. **`sorry`を選んで消す**
   - 簡単な補題から始める
   - ボトムアップで進む（Additive → Basic → Torsion → Field）

2. **証明を書く**
   - `#check` で利用可能な補題を探索
   - `exact?` で完全一致を検索
   - `apply?` でゴール指向の検索

3. **ローカルでテスト**
   ```bash
   lake build CyclotomicFunctionFields.Carlitz.Basic
   ```

4. **進捗をコミット**
   ```bash
   git add -A
   git commit -m "証明: [説明]"
   ```

## よく使うタクティク

- `intro x`: 変数を導入
- `apply h`: 仮定や補題を適用
- `exact h`: 正確な証明項を提供
- `rw [h]`: 等式を使って書き換え
- `simp`: simp補題を使って簡約化
- `ring`: 環の等式を解く
- `field_simp`: 体の式を簡約化
- `cases h`: 仮定に対してケース分割
- `induction x`: x に対して帰納法

## 参考資料

- Lean 4 マニュアル: https://leanprover.github.io/lean4/doc/
- Mathlib4 ドキュメント: https://leanprover-community.github.io/mathlib4_docs/
- Zulip チャット: https://leanprover.zulipchat.com/
- 定理証明支援系 Lean 4: https://aconite-ac.github.io/theorem_proving_in_lean4_ja/

## 主要論文

1. D. R. Hayes (1974). "Explicit Class Field Theory for Rational Function Fields."
   *Trans. AMS* 189: 77-91.

2. L. Carlitz (1935). "On Certain Functions Connected with Polynomials in a Galois Field."
   *Duke Math. J.* 1(2): 137-168.

3. D. Goss (1996). *Basic Structures of Function Field Arithmetic*. Springer.

## サポート

質問がある場合：
- Issueを開く
- Zulipで質問: https://leanprover.zulipchat.com/
- メーリングリストに投稿

## ライセンス

MIT License - 詳細は LICENSE ファイルを参照してください。

---

頑張ってください！ 🚀
