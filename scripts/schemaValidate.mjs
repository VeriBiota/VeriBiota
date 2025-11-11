import { readFile } from "node:fs/promises";
import process from "node:process";
import Ajv from "ajv";
import addFormats from "ajv-formats";

const ajv = new Ajv({ strict: true, allErrors: true });
addFormats(ajv);

async function validatePair(schemaPath, dataPath) {
  const schema = JSON.parse(await readFile(schemaPath, "utf8"));
  const data = JSON.parse(await readFile(dataPath, "utf8"));
  const validate = ajv.compile(schema);
  const valid = validate(data);
  if (valid) {
    console.log(`Validated ${dataPath} ✅`);
    return true;
  } else {
    console.error(`Validation failed for ${dataPath} ❌`);
    console.error(validate.errors);
    return false;
  }
}

const pairs = [
  ["schema/biolean.checks.v1.json", "build/artifacts/checks/sir-demo.json"],
  ["schema/biolean.certificate.v1.json", "build/artifacts/certificates/sir-demo.json"],
];

const results = await Promise.all(pairs.map(([schema, data]) => validatePair(schema, data)));
if (results.includes(false)) {
  process.exit(1);
}
