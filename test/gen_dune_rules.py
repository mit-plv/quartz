# ./dune calls this file in subdirectory run/ with tests in ..
import os
import glob

def generate_rules_for_file(path):
    src_path = os.path.splitext(path)[0]
    filename = os.path.basename(path)
    test_name = os.path.splitext(filename)[0]
    inner_func_name = f"{test_name}_inner"

    cpp_reject = False
    sv_reject = False
    with open(path, 'r') as f:
        first_line = f.readline().strip()
        if first_line.startswith("(*!") and first_line.endswith("*)"):
            content = first_line[3:-2].strip()
            if "cpp:reject" in content:
                cpp_reject = True
            if "sv:reject" in content:
                sv_reject = True

    print(f"""
; Rules for {test_name}

(rule
 (target {test_name}.out)
 (deps ../../lang/transform.vo {src_path}.vo ../../lang/pp.vo)
 (action
  (with-stdout-to %{{target}}
   (pipe-stdout
    (echo "Require Import quartz.lang.pp quartz.lang.Syntax quartz.lang.transform quartz.test.{test_name}. Import Strings.String.\\nLocal Open Scope string_scope.\\nCompute pp.bits (type.pack (fns.interp {test_name} (type.default _))).\\n")
    (run coqtop -q -Q .. quartz.test -Q ../../lang quartz.lang)
    (run python3 -c "import sys, re; s = sys.stdin.read(); m = re.search(r\\"=\\\\s*\\\\\\"(.*)\\\\\\\"(?:\\\\s*:\\\\s*string)?\\", s, re.DOTALL); sys.stdout.write((m.group(1).replace('\\\\\\\"\\\\\\\"', '\\\\\\\"') + chr(10)) if m else s)")))))

(rule
 (target {test_name}.sv)
 (deps ../../lang/sv.vo {src_path}.vo)
 (action
  (with-stdout-to %{{target}}
   (pipe-stdout
    (echo "Require Import quartz.lang.Syntax quartz.lang.sv quartz.test.{test_name}. Import Strings.String.\\nLocal Open Scope string_scope.\\nCompute sv.pp {test_name}.\\n")
    (run coqtop -q -Q .. quartz.test -Q ../../lang quartz.lang)
    (run python3 -c "import sys, re; s = sys.stdin.read(); m = re.search(r\\"=\\\\s*\\\\\\"(.*)\\\\\\\"(?:\\\\s*:\\\\s*string)?\\", s, re.DOTALL); sys.stdout.write((m.group(1).replace('\\\\\\\"\\\\\\\"', '\\\\\\\"') + chr(10)) if m else s)")))))

(rule
 (target {test_name}.cpp)
 (deps ../../lang/cpp.vo {src_path}.vo)
 (action
  (with-stdout-to %{{target}}
   (pipe-stdout
    (echo "Require Import quartz.lang.Syntax quartz.lang.cpp quartz.test.{test_name}. Import Strings.String.\\nLocal Open Scope string_scope.\\nCompute cpp.pp_test_driver (ltac:(repeat (constructor || cbn || discriminate))) {test_name}.\\n")
    (run coqtop -q -Q .. quartz.test -Q ../../lang quartz.lang)
    (run python3 -c "import sys, re; s = sys.stdin.read(); m = re.search(r\\"=\\\\s*\\\\\\"(.*)\\\\\\\"(?:\\\\s*:\\\\s*string)?\\", s, re.DOTALL); sys.stdout.write(m.group(1).replace('\\\\\\\"\\\\\\\"', '\\\\\\\"') if m else s)")))))

(rule
 (deps ../../slang/build/bin/slang {test_name}.sv)""")
    if sv_reject:
        print(f"""
 (alias test-sv)
 (action (with-accepted-exit-codes (not 0) (run ../../slang/build/bin/slang --quiet -Wno-missing-top {test_name}.sv --eval "{inner_func_name}(tt)"))))""")
    else:
        print(f"""
 (target {test_name}.sv_out)
 (action (with-stdout-to %{{target}} (run ../../slang/build/bin/slang --quiet -Wno-missing-top {test_name}.sv --eval "{inner_func_name}(tt)"))))

(rule (alias test-sv) (deps {test_name}.out {test_name}.sv_out) (action (diff {test_name}.out {test_name}.sv_out)))""")

    print(f"""
(rule
 (deps {test_name}.cpp)
 {"(alias test-cpp)" if cpp_reject else f"(target {test_name}.exe)"}
 (action
  (with-accepted-exit-codes {"(not 0)" if cpp_reject else "0"}
   (run c++ -fsanitize=address,undefined -std=c++2b -fbracket-depth=1024 {test_name}.cpp {"-fsyntax-only" if cpp_reject else "-o %{target}"}))))
""")

    if not cpp_reject:
        print(f"""
(rule
 (deps {test_name}.exe)
 (target {test_name}.cpp_out)
 (action (with-stdout-to %{{target}} (run ./{test_name}.exe))))

(rule (alias test-cpp) (deps {test_name}.out {test_name}.cpp_out) (action (diff {test_name}.out {test_name}.cpp_out)))
""")

if __name__ == "__main__":
    for f in glob.glob("../*.v"):
        generate_rules_for_file(f)
    print(f"""(alias (name runtest) (deps (alias test-sv)))""")
    print(f"""(alias (name runtest) (deps (alias test-cpp)))""")
