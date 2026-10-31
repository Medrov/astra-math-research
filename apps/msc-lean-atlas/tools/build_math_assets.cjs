'use strict';
// Deterministic, offline vendoring from the installed, pinned npm package.
const fs = require('node:fs');
const path = require('node:path');
const crypto = require('node:crypto');
const root = path.resolve(__dirname, '..');
const source = path.join(root, 'node_modules', 'katex');
const destination = path.join(root, 'web', 'vendor', 'katex');
const installed = JSON.parse(fs.readFileSync(path.join(source, 'package.json'), 'utf8'));
const requested = JSON.parse(fs.readFileSync(path.join(root, 'package.json'), 'utf8')).dependencies.katex;
if (installed.version !== requested) throw new Error('KaTeX must be installed at the exact package.json version.');
const fonts = fs.readdirSync(path.join(source, 'dist', 'fonts')).filter(name => /\.(woff2?|ttf)$/.test(name)).sort();
const files = [['dist/katex.min.js','katex.min.js'],['dist/katex.min.css','katex.min.css'],['LICENSE','LICENSE'],
  ...fonts.map(name => ['dist/fonts/' + name, 'fonts/' + name])];
fs.mkdirSync(destination, {recursive:true});
const manifest = {package:'katex',version:installed.version,license:installed.license,source:'node_modules/katex',files:{}};
for (const [input, output] of files) {
  const bytes = fs.readFileSync(path.join(source, input));
  const target = path.join(destination, output);
  fs.mkdirSync(path.dirname(target), {recursive:true});
  fs.writeFileSync(target, bytes);
  manifest.files[output] = {bytes:bytes.length,sha256:crypto.createHash('sha256').update(bytes).digest('hex')};
}
fs.writeFileSync(path.join(destination, 'manifest.json'), JSON.stringify(manifest, null, 2) + '\n');
console.log(`Vendored KaTeX ${installed.version}: ${files.length} files, including ${fonts.length} fonts.`);
