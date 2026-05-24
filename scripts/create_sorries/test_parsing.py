#!/usr/bin/env python3
"""
测试脚本：测试 LeanCodeParser 对复杂语法的解析能力
"""

from scripts.create_sorries.extract_sublemmas import LeanCodeParser, create_proof_with_sorries

def test_parsing():
    """测试各种复杂的 Lean 语法解析"""

    test_cases = [
        # 测试1: 包含默认参数的 lemma
        {
            "name": "默认参数测试",
            "code": """lemma pos_rpow_of_pos {x : ℝ≥0∞} {r : ℝ} (hx : x ≠ 0) (hr : 0 < r := by grind) :
    0 < x ^ r := by
  simpa +singlePass [← zero_rpow_of_pos hr, rpow_lt_rpow_iff hr] using by positivity""",
            "expected_statement": "lemma pos_rpow_of_pos {x : ℝ≥0∞} {r : ℝ} (hx : x ≠ 0) (hr : 0 < r := by grind) :\n    0 < x ^ r",
            "expected_proof": "by\n  simpa +singlePass [← zero_rpow_of_pos hr, rpow_lt_rpow_iff hr] using by positivity"
        },

        # 测试2: 简单的 theorem
        {
            "name": "简单 theorem 测试",
            "code": """theorem simple_example (a b : ℕ) : a + b = b + a := by
  exact add_comm a b""",
            "expected_statement": "theorem simple_example (a b : ℕ) : a + b = b + a",
            "expected_proof": "by\n  exact add_comm a b"
        },

        # 测试3: 证明中包含 have 语句
        {
            "name": "证明中包含 have 语句测试",
            "code": """lemma complex_proof (p q : Prop) (hp : p) (hq : q) : p ∧ q := by
  have h1 : p := hp
  have h2 : q := hq
  exact ⟨h1, h2⟩""",
            "expected_statement": "lemma complex_proof (p q : Prop) (hp : p) (hq : q) : p ∧ q",
            "expected_proof": "by\n  have h1 : p := hp\n  have h2 : q := hq\n  exact ⟨h1, h2⟩"
        },

        # 测试4: 多行 statement
        {
            "name": "多行 statement 测试",
            "code": """theorem long_statement (n : ℕ) (h : n > 0) :
    n * n > 0 := by
  exact Nat.mul_pos h h""",
            "expected_statement": "theorem long_statement (n : ℕ) (h : n > 0) :\n    n * n > 0",
            "expected_proof": "by\n  exact Nat.mul_pos h h"
        },

        # 测试5: 包含复杂类型参数的 lemma
        {
            "name": "复杂类型参数测试",
            "code": """lemma complex_types {α : Type*} [DecidableEq α] (s : Set α) (h : s.Nonempty) :
    ∃ x, x ∈ s := by
  exact h""",
            "expected_statement": "lemma complex_types {α : Type*} [DecidableEq α] (s : Set α) (h : s.Nonempty) :\n    ∃ x, x ∈ s",
            "expected_proof": "by\n  exact h"
        }
    ]

    print("=" * 60)
    print("LeanCodeParser 解析测试")
    print("=" * 60)

    for i, test_case in enumerate(test_cases, 1):
        print(f"\n测试 {i}: {test_case['name']}")
        print("-" * 40)

        try:
            parser = LeanCodeParser(test_case['code'])
            blocks = parser.extract_all_blocks(keys=["theorem", "lemma"])

            if blocks:
                block = blocks[0]
                info = block['info']

                print(f"✓ 成功解析")
                print(f"名称: {info['name']}")
                print(f"证明风格: {info['proof_style']}")
                print(f"包含 sorry: {info['with_sorry']}")
                print(f"\nStatement:")
                print(f"'{info['statement']}'")
                print(f"\nProof:")
                print(f"'{info['proof']}'")

                # 检查是否符合预期
                if info['statement'].strip() == test_case['expected_statement'].strip():
                    print("✓ Statement 解析正确")
                else:
                    print("✗ Statement 解析错误")
                    print(f"期望: '{test_case['expected_statement']}'")

                if info['proof'].strip() == test_case['expected_proof'].strip():
                    print("✓ Proof 解析正确")
                else:
                    print("✗ Proof 解析错误")
                    print(f"期望: '{test_case['expected_proof']}'")

            else:
                print("✗ 未能解析出任何 block")

        except Exception as e:
            print(f"✗ 解析出错: {e}")

        print()

def test_sorry_replacement():
    """测试 sorry 替换功能"""

    print("=" * 60)
    print("Sorry 替换测试")
    print("=" * 60)

    test_code = """lemma test_lemma (a b : ℕ) : a + b = b + a := by
  exact add_comm a b

theorem test_theorem (p : Prop) : p → p := by
  intro h
  exact h"""

    print("原始代码:")
    print(test_code)
    print("\n" + "-" * 40)

    try:
        result = create_proof_with_sorries(test_code, keys=["theorem", "lemma"])
        print("替换后的代码:")
        print(result)
        print("\n✓ Sorry 替换成功")
    except Exception as e:
        print(f"✗ Sorry 替换失败: {e}")

if __name__ == "__main__":
    test_parsing()
    test_sorry_replacement()
