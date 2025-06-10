#!/usr/bin/env python3
"""
脚本功能：
1. 遍历当前目录及子目录中的.lean文件
2. 排除blocklist中的文件和隐藏目录
3. 找到只有空格+classical+换行的行并删除
4. 在前面第一个空行下插入"open Classical in"
5. 统计处理的文件数量
"""

import os
import fnmatch
import re
from pathlib import Path

# 定义blocklist
BLOCKLIST = [
    "Mathlib/Tactic/Have.lean",  # skip a specific file
    "Archive.lean",
    "Counterexamples.lean",
    "docs.lean",
    "lakefile.lean",
    "Mathlib.lean",
]

def blocked(rel_path: str) -> bool:
    """Check if a path should be blocked from processing."""
    # skip hidden dirs / files at any depth
    if any(seg.startswith('.') for seg in rel_path.split('/')):
        return True
    # skip user-defined patterns
    return any(fnmatch.fnmatch(rel_path, pat) for pat in BLOCKLIST)

def process_lean_file(file_path: Path) -> int:
    """
    处理单个.lean文件，返回删除的classical行数
    """
    try:
        # 读取文件内容
        with open(file_path, 'r', encoding='utf-8') as f:
            lines = f.readlines()

        modified = False
        classical_count = 0
        new_lines = []
        i = 0

        while i < len(lines):
            line = lines[i]

            # 检查是否是符合条件的classical行
            # 条件：前面只有空格，classical，后面紧跟换行
            if re.match(r'^\s*classical\s*$', line):
                classical_count += 1
                modified = True

                # 往回找第一个完全空行
                insert_pos = -1
                for j in range(len(new_lines) - 1, -1, -1):
                    if new_lines[j].strip() == '':  # 完全空行
                        insert_pos = j + 1
                        break

                # 如果没找到空行，在文件开头插入
                if insert_pos == -1:
                    insert_pos = 0

                # 在空行下面插入"open Classical in"
                new_lines.insert(insert_pos, "open Classical in\n")

                # 跳过当前classical行（不加入new_lines）
                i += 1
                continue

            # 正常行加入结果
            new_lines.append(line)
            i += 1

        # 如果有修改，写回文件
        if modified:
            with open(file_path, 'w', encoding='utf-8') as f:
                f.writelines(new_lines)
            print(f"已处理文件: {file_path} (删除了 {classical_count} 个classical)")

        return classical_count

    except Exception as e:
        print(f"处理文件 {file_path} 时出错: {e}")
        return 0

def main():
    """主函数"""
    current_dir = Path('.')
    total_classical_count = 0
    processed_files = 0

    print("开始处理.lean文件...")
    print(f"当前目录: {current_dir.absolute()}")
    print("-" * 50)

    # 遍历所有.lean文件
    for root, dirs, files in os.walk(current_dir):
        # 过滤掉隐藏目录
        dirs[:] = [d for d in dirs if not d.startswith('.')]

        for file in files:
            if file.endswith('.lean'):
                file_path = Path(root) / file
                rel_path = file_path.relative_to(current_dir)

                # 检查是否被blocked
                if blocked(str(rel_path)):
                    print(f"跳过blocked文件: {rel_path}")
                    continue

                # 处理文件
                classical_count = process_lean_file(file_path)
                if classical_count > 0:
                    processed_files += 1
                    total_classical_count += classical_count

    print("-" * 50)
    print(f"处理完成!")
    print(f"共处理了 {processed_files} 个文件")
    print(f"总共删除了 {total_classical_count} 个classical行")

if __name__ == "__main__":
    main()
