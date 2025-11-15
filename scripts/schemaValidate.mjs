// scripts/schemaValidate.mjs
import fs from 'node:fs';
import Ajv from 'ajv';
import addFormats from 'ajv-formats';

const ajv = new Ajv({
  allErrors: true,
  strict: true,
  // Our schemas use `type: ["X","null"]` unions; allow them explicitly.
  allowUnionTypes: true,
});
addFormats(ajv);

function load(p) { return JSON.parse(fs.readFileSync(p, 'utf8')); }

const checksSchema = load('schema/veribiota.checks.v1.json');
const certSchema   = load('schema/veribiota.certificate.v1.json');
const validateChecks = ajv.compile(checksSchema);
const validateCert   = ajv.compile(certSchema);

const [checksPath = 'releases/pilot-demo-v1/outputs/checks.json',
       certPath   = 'releases/pilot-demo-v1/certificates/certificate.json'] = process.argv.slice(2);

for (const [name, file, validate] of [
  ['checks', checksPath, validateChecks],
  ['certificate', certPath, validateCert],
]) {
  const data = load(file);
  const ok = validate(data);
  if (!ok) {
    console.error(`❌ ${name} failed schema validation: ${file}`);
    console.error(validate.errors);
    process.exitCode = 1;
  } else {
    console.log(`✅ ${name} valid: ${file}`);
  }
}
