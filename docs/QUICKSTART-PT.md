# Como instalar, verificar e publicar

O pacote inicial é um repositório Git transportável, `MahlerLeanII.bundle`.
Ele contém um commit inicial e todos os arquivos do projeto. A criação do
repositório remoto ainda depende de autenticação no GitHub. As provas Lean
incluídas são candidatas e ainda precisam compilar.

## 1. Baixar e instalar

Salve `MahlerLeanII.bundle` na pasta Downloads. Os comandos abaixo pressupõem
macOS com Homebrew. Se você já usa Lean na Parte I, pode manter a instalação
existente; o arquivo `lean-toolchain` seleciona a versão deste projeto.

```bash
brew install elan-init gh
git clone "$HOME/Downloads/MahlerLeanII.bundle" "$HOME/Desktop/MahlerLeanII"
cd "$HOME/Desktop/MahlerLeanII"
git remote remove origin
git config user.name "Diego Marques"
git config user.email "321085351+DiegoMarquesMath@users.noreply.github.com"
```

O clone recusa substituir uma pasta já existente. Não é necessário rodar
`git init`: o histórico do Git está no bundle. Remover `origin` retira apenas
a referência ao arquivo local, para que o GitHub possa se tornar o remoto.

## 2. Executar a verificação

```bash
lake exe cache get
bash scripts/check.sh
```

O comando pode apontar erros nas provas iniciais. Isso não significa que o
artigo esteja errado; significa que ainda precisamos corrigir ou concluir
a tradução formal. O diagnóstico completo fica em `build/verification.log`.
Não substitua provas por `sorry` para obter uma compilação aparente.

Sucesso exige que o comando termine sem erro e imprima:

```text
Build and axiom audit passed for the current declared scope.
```

Mesmo nesse caso, o escopo inicial se limita à definição e aos lemas descritos
em `docs/STATUS.md`.

## 3. Criar e publicar no GitHub

É possível publicar o repositório de desenvolvimento antes de concluir a
formalização, mantendo seu estado pendente explícito no README.

```bash
gh auth login --hostname github.com --git-protocol https --web
gh api user --jq .login
```

A segunda linha deve mostrar `DiegoMarquesMath`. Se outra conta estiver ativa
e a conta correta já tiver sido autenticada, use:

```bash
gh auth switch --hostname github.com --user DiegoMarquesMath
```

Crie o repositório público e envie o commit:

```bash
gh repo create DiegoMarquesMath/MahlerLeanII \
  --public --source=. --remote=origin --push \
  --description "Lean 4 formalization project for Mahler's Problem on Liouville Numbers II. Rational Maps"
```

Se o repositório já tiver sido criado, não crie outro. Confira que ele está
vazio e pertence à conta correta antes de usar:

```bash
git remote add origin https://github.com/DiegoMarquesMath/MahlerLeanII.git
git push -u origin main
```

Se houver commits remotos, faça a integração normalmente; não use force-push.

## 4. Conferir a execução remota

```bash
gh run list --repo DiegoMarquesMath/MahlerLeanII --limit 5
gh repo view DiegoMarquesMath/MahlerLeanII --web
```

Na aba **Actions**, abra a execução correspondente ao commit enviado. Confira
o resultado da etapa **Build and audit all project declarations**. Uma execução
com erro ou ainda em andamento não é uma verificação concluída.

## 5. Continuar a formalização

Abra esta pasta no Codex que você já utiliza. Uma instrução inicial adequada é:

> Leia AGENTS.md e docs/STATUS.md. Compile o projeto com as versões fixadas,
> corrija as provas iniciais sem alterar os enunciados, sem sorry e sem axiomas
> adicionais, e execute scripts/check.sh. Depois formalize o Lema 2.2 e a
> Proposição 2.3 do manuscrito, preservando a definição de aproximação em todas
> as escalas suficientemente grandes. Registre precisamente o que compilou e
> o que ainda não foi formalizado.

Forneça ao Codex a versão correspondente do manuscrito, que não está incluída
neste repositório. Só prossiga para resultados posteriores depois de resolver
os erros das etapas anteriores. O plano está em `docs/ROADMAP.md`.

## 6. Preparar a versão citável

Depois de a compilação, a auditoria e a correspondência com o artigo serem
conferidas, atualize o estado dos resultados e `CITATION.cff`, faça um commit,
envie-o e confirme que esse commit passou no GitHub Actions. Crie então uma
release com nome próprio, por exemplo `v0.1.0`, apontando para esse commit.
Os modelos de redação e referência estão em `docs/CITATION.md`.

Fontes dos comandos: [elan no Homebrew](https://formulae.brew.sh/formula/elan-init),
[criação com GitHub CLI](https://cli.github.com/manual/gh_repo_create) e
[validação de provas Lean](https://lean-lang.org/doc/reference/latest/ValidatingProofs/).
