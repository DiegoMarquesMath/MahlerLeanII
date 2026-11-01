# Reproduzir a verificação do Teorema 1.2

Com elan instalado, execute na pasta do projeto.

```bash
lake exe cache get
bash scripts/check.sh
```

Para localizar a declaração principal na auditoria, execute

```bash
grep 'AUDITED MahlerLeanII.rational_classification:' build/verification.log
```

O teorema está em [Classification.lean](../MahlerLeanII/Classification.lean).
A [correspondência com o artigo](STATUS.md) identifica as três condições
e distingue a classificação da conclusão de Cantor do Teorema 1.3.
O [modelo de citação](CITATION.md) usa o hash da versão auditada.
