# AJ Conjecture Formalization and Comparator Results

This repository is the working home for the AJ project's Lean formalization, comparator inputs, and verification records. It starts private and is intended for later public release.

## Starting points

- [Existing Lean development and scope](https://github.com/DavetheSlayer/aj-conjecture-audit/tree/c5f40ea6ce55931bb19645e40a30528b2e32f5fb/formalization)
- [Accepted single-example comparator report](https://github.com/DavetheSlayer/aj-conjecture-audit/blob/418b3ed892825dd595011ef5d35e62fd54eeeb22/formalization/reports/comparator-2026-11-15.md)
- [Four-family written theorem and Lean handoff](https://github.com/DavetheSlayer/aj-conjecture-audit/tree/e4a4786b01dec67c542924d82a4c1a2378e6a05d/handoffs/2026-11-18-whitehead-four-family)

## Adding a formalization or comparator result

For Lean changes, record the theorem names and their scope, the Lean toolchain, and dependency pins. For comparator runs, record the exact tested commit and config, the command, the kernel or sandbox versions, the outcome, and the log or a stable reference to it. Label local builds and comparator runs separately so readers can tell exactly what was checked. If a result is imported from the audit repository, retain its original commit and report references.

## 给李金政

请在本库上传 Lean 源码、比较器（comparator）的配置和运行报告。报告请注明被验证的提交、定理范围、工具链和依赖版本、运行命令及结果，并附日志或可追溯的记录。请分别标明本地构建和 comparator 验证的范围。迁移已有结果时，请保留原始提交和报告的链接。

[中文交接指南](https://github.com/DavetheSlayer/aj-conjecture-audit/blob/e4a4786b01dec67c542924d82a4c1a2378e6a05d/handoffs/2026-11-18-whitehead-four-family/FOR_JINZHENG_%E4%B8%AD%E6%96%87.md)
