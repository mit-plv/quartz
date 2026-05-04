# ./dune calls this file in subdirectory run/ with tests in ..
import os
import glob

def generate_rules_for_file(path):
    src_path = os.path.splitext(path)[0]
    filename = os.path.basename(path)
    test_name = os.path.splitext(filename)[0]
    inner_func_name = f"{test_name}_inner"

    print(f"""
; Rules for {test_name}

(rule
 (target {test_name}.out)
 (deps ../../lang/transform.vo {src_path}.vo)
 (action
  (with-stdout-to %{{target}}
   (pipe-stdout
    (echo "Require Import quartz.lang.domain quartz.lang.Syntax quartz.lang.transform quartz.test.{test_name}. Import Strings.String.\\nLocal Open Scope string_scope.\\nCompute bits.hex (type.pack (fns.interp {test_name} (type.default _))).\\n")
    (run coqtop -q -Q .. quartz.test -Q ../../lang quartz.lang)
    (run python3 -c "import sys, re; s = sys.stdin.read(); m = re.search(r\\"=\\\\s*\\\\\\"(.*)\\\\\\\"(?:\\\\s*:\\\\s*string)?\\", s, re.DOTALL); sys.stdout.write((m.group(1).replace('\\\\\\\"\\\\\\\"', '\\\\\\\"') + chr(10)) if m else s)")))))

(rule
 (target {test_name}.sv)
 (deps ../../lang/sv.vo {src_path}.vo)
 (action
  (with-stdout-to %{{target}}
   (pipe-stdout
    (echo "Require Import quartz.lang.Syntax quartz.lang.sv quartz.test.{test_name}. Import String.\\nLocal Open Scope string_scope.\\nCompute sv.pp {test_name}.\\n")
    (run coqtop -q -Q .. quartz.test -Q ../../lang quartz.lang)
    (run python3 -c "import sys, re; s = sys.stdin.read(); m = re.search(r\\"=\\\\s*\\\\\\"(.*)\\\\\\\"(?:\\\\s*:\\\\s*string)?\\", s, re.DOTALL); sys.stdout.write((m.group(1).replace('\\\\\\\"\\\\\\\"', '\\\\\\\"') + chr(10)) if m else s)")))))

(rule
 (target {test_name}.sv_out)
 (deps ../../slang/build/bin/slang {test_name}.sv)
 (action (with-stdout-to %{{target}}
   (pipe-stdout
    (run ../../slang/build/bin/slang --quiet -Wno-missing-top {test_name}.sv --eval "{inner_func_name}(tt)")
    (run python3 -c "import sys, re; s = sys.stdin.read(); m = re.search(r\\"([0-9]+)'s?h([0-9a-fA-F]+)\\", s); sys.stdout.write((m.group(2) + chr(10)) if m else s)")))))

(rule
 (target {test_name}.cpp)
 (deps ../../lang/cpp.vo {src_path}.vo)
 (action
  (with-stdout-to %{{target}}
   (pipe-stdout
    (echo "Require Import quartz.lang.Syntax quartz.lang.cpp quartz.test.{test_name}. Import String.\\nLocal Open Scope string_scope.\\nCompute cpp.pp_test_driver (ltac:(repeat (constructor || cbn || discriminate))) {test_name}.\\n")
    (run coqtop -q -Q .. quartz.test -Q ../../lang quartz.lang)
    (run python3 -c "import sys, re; m = re.search(r\\"=\\\\s*\\\\\\"(.*)\\\\\\\"(?:\\\\s*:\\\\s*string)?\\", sys.stdin.read(), re.DOTALL); sys.stdout.write(m.group(1).replace('\\\\\\\"\\\\\\\"', '\\\\\\\"') if m else '')")))))

(rule
 (target {test_name}.exe)
 (deps {test_name}.cpp)
 (action (run c++ -fsanitize=address,undefined -std=c++2b {test_name}.cpp -o %{{target}})))

(rule
 (target {test_name}.cpp_out)
 (deps {test_name}.exe)
 (action (with-stdout-to %{{target}} (run ./{test_name}.exe))))

(rule
 (alias runtest)
 (deps {test_name}.cpp_out {test_name}.sv_out {test_name}.out)
 (action (progn
   (diff {test_name}.out {test_name}.cpp_out)
   (diff {test_name}.out {test_name}.sv_out)
 )))
""")

if __name__ == "__main__":
    for f in glob.glob("../*.v"):
        generate_rules_for_file(f)
