import { readFile } from "node:fs/promises";
import path from "node:path";
import { fileURLToPath } from "node:url";
import { globSync } from "glob";
import YAML from "yaml";
import Ajv2020 from "ajv/dist/2020.js";

const __filename = fileURLToPath(import.meta.url);
const __dirname = path.dirname(__filename);
const repoRoot = path.resolve(__dirname, "..");

const schemaPath = path.join(repoRoot, "schemas", "task.schema.json");
const schema = JSON.parse(await readFile(schemaPath, "utf8"));

const ajv = new Ajv2020({ allErrors: true, strict: false });
const validate = ajv.compile(schema);

const taskFiles = globSync("tasks/*.task.md", { cwd: repoRoot });

let hasError = false;

function parseFrontMatter(content) {
  if (!content.startsWith("---")) {
    throw new Error("missing front matter delimiter");
  }
  const end = content.indexOf("\n---", 3);
  if (end === -1) {
    throw new Error("unterminated front matter block");
  }
  const yamlBlock = content.slice(4, end).trim();
  return YAML.parse(yamlBlock);
}

for (const relPath of taskFiles) {
  const absPath = path.join(repoRoot, relPath);
  const raw = await readFile(absPath, "utf8");
  let data;
  try {
    data = parseFrontMatter(raw);
  } catch (err) {
    console.error(`Failed to parse front matter for ${relPath}:`, err.message);
    hasError = true;
    continue;
  }
  const ok = validate(data);
  if (!ok) {
    hasError = true;
    console.error(`Schema validation failed for ${relPath}:`);
    for (const issue of validate.errors ?? []) {
      console.error(`  - ${issue.instancePath} ${issue.message}`);
    }
  }
}

if (hasError) {
  process.exit(1);
}
