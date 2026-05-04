diff --git a/tools/driver/slang_main.cpp b/tools/driver/slang_main.cpp
index 51db4a7fc..3a546c050 100644
--- a/tools/driver/slang_main.cpp
+++ b/tools/driver/slang_main.cpp
@@ -9,12 +9,16 @@
 #include <iostream>
 
 #include "slang/analysis/AnalysisManager.h"
+#include "slang/ast/ASTContext.h"
 #include "slang/ast/ASTSerializer.h"
 #include "slang/ast/Compilation.h"
+#include "slang/ast/EvalContext.h"
+#include "slang/ast/Expression.h"
 #include "slang/ast/symbols/CompilationUnitSymbols.h"
 #include "slang/diagnostics/TextDiagnosticClient.h"
 #include "slang/driver/Driver.h"
 #include "slang/driver/MemoryStats.h"
+#include "slang/syntax/AllSyntax.h"
 #include "slang/syntax/CSTSerializer.h"
 #include "slang/syntax/SyntaxTree.h"
 #include "slang/text/Json.h"
@@ -177,6 +181,7 @@ int driverMain(int argc, TArgs argv) {
         std::optional<bool> onlyMacros;
         std::optional<bool> disableAnalysis;
         std::optional<bool> groupMacrosByFile;
+        std::optional<std::string> evalExpr;
         driver.cmdLine.add("-E,--preprocess", onlyPreprocess,
                            "Only run the preprocessor (and print preprocessed files to stdout)");
         driver.cmdLine.add("--macros-only", onlyMacros, "Print a list of found macros and exit");
@@ -188,6 +193,8 @@ int driverMain(int argc, TArgs argv) {
         driver.cmdLine.add("--disable-analysis", disableAnalysis,
                            "Disables post-elaboration analysis passes,"
                            "which prevents some diagnostics from being issued");
+        driver.cmdLine.add("--eval", evalExpr,
+                           "Evaluate the given expression and print the result", "<expression>");
 
         std::optional<bool> includeComments;
         std::optional<bool> includeDirectives;
@@ -337,6 +344,39 @@ int driverMain(int argc, TArgs argv) {
                 driver.reportCompilation(*compilation, quiet == true);
             }
 
+            if (evalExpr) {
+                compilation->unfreeze();
+                auto exprTree = SyntaxTree::fromText(*evalExpr, driver.sourceManager, "source", "", driver.createOptionBag());
+
+                auto cus = compilation->getCompilationUnits();
+                const Scope* evalScope = cus.empty() ? (const Scope*)&compilation->getRoot() : (const Scope*)cus.back();
+                ASTContext astCtx(*evalScope, LookupLocation::max);
+                EvalContext evalContext(astCtx, EvalFlags::IsScript);
+                evalContext.pushEmptyFrame();
+
+                ConstantValue result;
+                if (auto expr = exprTree->root().as_if<ExpressionSyntax>()) {
+                    auto& bound = Expression::bind(*expr, astCtx, ASTFlags::AssignmentAllowed);
+                    if (bound.kind == ExpressionKind::Invalid) {
+                        driver.printError("expression passed to --eval failed to bind (check for undeclared identifiers or type mismatches)");
+                    } else {
+                        result = bound.eval(evalContext);
+                    }
+                } else {
+                    driver.printError("argument to --eval is not a valid expression");
+                }
+
+                evalContext.reportAllDiags();
+                driver.diagEngine.issue(exprTree->diagnostics());
+                driver.diagEngine.issue(evalContext.getAllDiagnostics());
+
+                if (!result.bad()) {
+                    OS::print(fmt::format("{}\n", result.isInteger() ? 
+                        result.integer().toString(slang::LiteralBase::Hex, true) : result.toString()));
+                }
+                compilation->freeze();
+            }
+
             std::unique_ptr<analysis::AnalysisManager> analysisManager;
             if (!disableAnalysis.value_or(false)) {
                 TimeTraceScope timeScope("semanticAnalysis"sv, ""sv);
