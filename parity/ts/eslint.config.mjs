import tsPlugin from "@typescript-eslint/eslint-plugin"
import tsParser from "@typescript-eslint/parser"
import recommended from "eslint-config-functype/recommended"
import functype from "eslint-plugin-functype"
import prettier from "eslint-plugin-prettier"
import simpleImportSort from "eslint-plugin-simple-import-sort"

// TODO(functype): eslint-config-functype's `recommended` sets rules only. It registers no
// parser, plugins or `files`, so its README's `export default [recommended]` lints no .ts
// files on ESLint 10. This block supplies them.
export default [
  { ignores: ["dist/**", "node_modules/**"] },
  {
    files: ["src/**/*.ts"],
    languageOptions: {
      parser: tsParser,
      parserOptions: { projectService: true, tsconfigRootDir: import.meta.dirname },
    },
    plugins: { "@typescript-eslint": tsPlugin, prettier, "simple-import-sort": simpleImportSort },
  },
  { files: ["src/**/*.ts"], ...recommended },
  { files: ["src/**/*.ts"], ...functype.configs.recommended },
]
