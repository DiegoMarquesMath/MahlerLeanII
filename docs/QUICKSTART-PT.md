# Reproduzir a verificação

Com elan instalado, clone o repositório e rode os comandos abaixo na pasta
do projeto.

```bash
lake exe cache get
bash scripts/check.sh
```

O resultado fica em `build/verification.log`. Em 31 de outubro de 2026,
o autor executou o script em seu Mac com Lean 4.24.0 e as 23 declarações
exigidas pela auditoria passaram. O [registro da seção 4](SECTION4.md)
identifica as provas correspondentes ao determinante de reconstrução.

Para citar o código, abra a aba **Actions** no GitHub, confira que a execução
**Lean verification** passou no commit escolhido e use o hash completo desse
commit conforme o [modelo de referência](CITATION.md).
