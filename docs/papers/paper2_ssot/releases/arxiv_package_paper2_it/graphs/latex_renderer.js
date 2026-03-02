/**
 * LaTeX Renderer Module
 * 
 * Extracts and renders LaTeX math from Lean theorem statements.
 * Uses KaTeX CDN for rendering.
 */

const LATEX_MAPPING = {
  'Nat': '\\mathbb{N}',
  'Int': '\\mathbb{Z}',
  'Bool': '\\mathbb{B}',
  'Prop': '\\text{Prop}',
  'Type': '\\text{Type}',
  'List': '\\text{List}',
  'Array': '\\text{Array}',
  'Finset': '\\mathcal{F}',
  'Set': '\\mathcal{S}',
  'Real': '\\mathbb{R}',
  'forall': '\\forall',
  'exists': '\\exists',
  '->': '\\rightarrow',
  '->': '\\to',
  '\\/': '\\lor',
  '/\\': '\\land',
  '~': '\\neg',
  '<=': '\\leq',
  '>=': '\\geq',
  '!=': '\\neq',
  '==': '\\equiv',
};

const LEAN_TO_LATEX_PATTERNS = [
  [/Nat\.add/g, '\\mathbb{N}.+'],
  [/Nat\.mul/g, '\\mathbb{N}.\\times'],
  [/Nat\.sub/g, '\\mathbb{N}.-'],
  [/Nat\.le/g, '\\le_{\\mathbb{N}}'],
  [/Int\.add/g, '\\mathbb{Z}.+'],
  [/List\.append/g, '\\mathbin{+\\!+}'],
  [/List\.map/g, '\\text{map}'],
  [/Finset\.card/g, '|\\cdot|'],
  [/Finset\.union/g, '\\cup'],
  [/Finset\.inter/g, '\\cap'],
  [/\bforall\b/g, '\\forall'],
  [/\bexists\b/g, '\\exists'],
  [/\bTrue\b/g, '\\top'],
  [/\bFalse\b/g, '\\bot'],
  [/\bAnd\b/g, '\\land'],
  [/\bOr\b/g, '\\lor'],
  [/\bNot\b/g, '\\neg'],
  [/\bEq\b/g, '='],
  [/->/g, '\\to'],
  [/=>/g, '\\Rightarrow'],
  [/<->/g, '\\leftrightarrow'],
  [/<=/g, '\\leq'],
  [/>=/g, '\\geq'],
  [/!=/g, '\\neq'],
];

export function leanToLatex(leanCode) {
  if (!leanCode) return null;
  
  let latex = leanCode
    .replace(/^theorem\s+/, '\\textbf{Theorem:} ')
    .replace(/^lemma\s+/, '\\textbf{Lemma:} ')
    .replace(/^def\s+/, '\\textbf{Def:} ')
    .replace(/^axiom\s+/, '\\textbf{Axiom:} ')
    .replace(/\s*:\s*/g, ' : ')
    .replace(/\s*:=\s*/g, ' := ');
  
  for (const [pattern, replacement] of LEAN_TO_LATEX_PATTERNS) {
    latex = latex.replace(pattern, replacement);
  }
  
  latex = latex
    .replace(/([a-zA-Z_][a-zA-Z0-9_]*)\s*\(/g, '\\text{$1}(')
    .replace(/\(([^)]+)\)/g, '\\($1\\)');
  
  return `\\text{${latex}}`;
}

export function extractLatex(node) {
  if (!node) return null;
  
  if (node.latex) return node.latex;
  if (node.signature) return leanToLatex(node.signature);
  if (node.statement) return leanToLatex(node.statement);
  
  const name = node.id?.split('.').pop() || '';
  const kind = node.kind || 'node';
  
  return `\\text{${kind}\\ ${name}}`;
}

export function renderLatex(latex, container) {
  if (!latex || !container) return false;
  
  if (typeof window !== 'undefined' && window.katex) {
    try {
      window.katex.render(latex, container, {
        throwOnError: false,
        displayMode: true,
        output: 'html',
      });
      return true;
    } catch (e) {
      container.textContent = latex;
      return false;
    }
  }
  
  container.textContent = latex;
  return false;
}

export function renderLatexInline(latex, container) {
  if (!latex || !container) return false;
  
  if (typeof window !== 'undefined' && window.katex) {
    try {
      window.katex.render(latex, container, {
        throwOnError: false,
        displayMode: false,
        output: 'html',
      });
      return true;
    } catch (e) {
      container.textContent = latex;
      return false;
    }
  }
  
  container.textContent = latex;
  return false;
}

export function formatLeanSignature(signature, maxLength = 200) {
  if (!signature) return null;
  
  const trimmed = signature.trim();
  if (trimmed.length <= maxLength) return trimmed;
  
  return trimmed.slice(0, maxLength - 3) + '...';
}

export const FOUNDATION_BUCKETS = {
  'FOUNDATION.Counting': {
    name: 'Counting',
    description: 'Nat, Int, Fin (counting structure)',
    color: '#ef4444',
    symbols: ['Nat', 'Int', 'Fin', 'Nat.add', 'Nat.mul', 'Nat.sub'],
  },
  'FOUNDATION.Collections': {
    name: 'Collections',
    description: 'List, Array, Finset (collection structure)',
    color: '#3b82f6',
    symbols: ['List', 'Array', 'Finset', 'List.append', 'List.map'],
  },
  'FOUNDATION.Boolean': {
    name: 'Boolean',
    description: 'Bool (branching structure)',
    color: '#f59e0b',
    symbols: ['Bool', 'Bool.true', 'Bool.false'],
  },
  'FOUNDATION.Logic': {
    name: 'Logic',
    description: 'True, False, And, Or, Exists (logical structure)',
    color: '#8b5cf6',
    symbols: ['True', 'False', 'And', 'Or', 'Exists', 'Decidable'],
  },
  'FOUNDATION.Equality': {
    name: 'Equality',
    description: 'Eq, HEq, Decidable (equality structure)',
    color: '#10b981',
    symbols: ['Eq', 'HEq', 'Decidable'],
  },
  'FOUNDATION.SetTheory': {
    name: 'Set Theory',
    description: 'Set, Membership, Quot (set structure)',
    color: '#ec4899',
    symbols: ['Set', 'Membership', 'Quot'],
  },
  'FOUNDATION.OrderAlgebra': {
    name: 'Order/Algebra',
    description: 'LT, LE, Add, Mul (order/algebra)',
    color: '#06b6d4',
    symbols: ['LT', 'LE', 'Add', 'Mul', 'Semiring'],
  },
  'FOUNDATION.MeasureTheory': {
    name: 'Measure Theory',
    description: 'MeasureTheory, ProbabilityTheory',
    color: '#f97316',
    symbols: ['MeasureTheory', 'ProbabilityTheory', 'Measure'],
  },
  'FOUNDATION.Analysis': {
    name: 'Analysis',
    description: 'Real, NNReal, Complex (analytic structure)',
    color: '#a855f7',
    symbols: ['Real', 'NNReal', 'Complex'],
  },
};

export function classifyFoundationBucket(nodeId) {
  const id = nodeId.toLowerCase();
  
  for (const [bucket, info] of Object.entries(FOUNDATION_BUCKETS)) {
    for (const symbol of info.symbols) {
      if (id.includes(symbol.toLowerCase())) {
        return bucket;
      }
    }
  }
  
  if (id.includes('nat') || id.includes('int') || id.includes('fin')) {
    return 'FOUNDATION.Counting';
  }
  if (id.includes('list') || id.includes('array') || id.includes('finset')) {
    return 'FOUNDATION.Collections';
  }
  if (id.includes('bool')) {
    return 'FOUNDATION.Boolean';
  }
  if (id.includes('true') || id.includes('false') || id.includes('and') || 
      id.includes('or') || id.includes('exists') || id.includes('decidable')) {
    return 'FOUNDATION.Logic';
  }
  if (id.includes('eq') || id.includes('heq')) {
    return 'FOUNDATION.Equality';
  }
  if (id.includes('set') || id.includes('membership') || id.includes('quot')) {
    return 'FOUNDATION.SetTheory';
  }
  if (id.includes('lt') || id.includes('le') || id.includes('add') || id.includes('mul')) {
    return 'FOUNDATION.OrderAlgebra';
  }
  if (id.includes('measure') || id.includes('probability')) {
    return 'FOUNDATION.MeasureTheory';
  }
  if (id.includes('real') || id.includes('complex')) {
    return 'FOUNDATION.Analysis';
  }
  
  return null;
}

export function computeFoundationBuckets(nodeId, dependencies, data) {
  const buckets = new Set();
  
  const directBucket = classifyFoundationBucket(nodeId);
  if (directBucket) buckets.add(directBucket);
  
  if (dependencies && data) {
    const traverse = (id, visited = new Set()) => {
      if (visited.has(id)) return;
      visited.add(id);
      
      const bucket = classifyFoundationBucket(id);
      if (bucket) buckets.add(bucket);
      
      const node = data.nodes.find(n => n.id === id);
      if (node && node.kind === 'axiom') {
        if (id.startsWith('FOUNDATION.')) {
          buckets.add(id);
        }
      }
      
      const deps = dependencies[id] || [];
      for (const dep of deps) {
        traverse(dep, visited);
      }
    };
    
    traverse(nodeId);
  }
  
  return Array.from(buckets);
}
