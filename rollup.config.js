import babel from '@rollup/plugin-babel';
import commonjs from '@rollup/plugin-commonjs';
import external from 'rollup-plugin-peer-deps-external';
import postcss from 'rollup-plugin-postcss';
import resolve from '@rollup/plugin-node-resolve';
import visualizer from 'rollup-plugin-visualizer';

import * as pkg from './package.json' assert { type: "json" };

export default {
  input: './src/lib/index.js',
  output: [
    {
      file: pkg.default.main,
      format: 'cjs'
    },
    {
      file: pkg.default.module,
      format: 'esm'
    }
  ],
  plugins: [
    external(),
    postcss(),
    babel({
      exclude: 'node_modules/**'
    }),
    resolve(),
    commonjs(),
    visualizer()
  ]
};
