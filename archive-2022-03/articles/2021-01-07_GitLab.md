# memo

GitLab CI/CD についてメモをします。

## CI

GitLab CI/CD は、見た目はゴテゴテしていて分かりにくいように見えました。しかし、しっかり公式のドキュメントを読んでみれば、どういうものなのか分かってきました。

```yml
build-job:
  stage: build
  script:
    - echo "Hello, $GITLAB_USER_LOGIN!"

test-job1:
  stage: test
  script:
    - echo "This job tests something"

test-job2:
  stage: test
  script:
    - echo "This job tests something, but takes more time than test-job1."
    - echo "After the echo commands complete, it runs the sleep command for 20 seconds"
    - echo "which simulates a test that runs 20 seconds longer than test-job1"
    - sleep 20

deploy-prod:
  stage: deploy
  script:
    - echo "This job deploys something from the $CI_COMMIT_BRANCH branch."
```

[Get starged with GitLab CI/CD | GitLab](https://docs.gitlab.com/ee/ci/quick_start/README.html) によると、基本形は上記のような YAML になっています。ここから少し変更を始めていくことにします。

[Create a GitLab Pages website from scratch | GitLab](https://docs.gitlab.com/ee/user/project/pages/getting_started/pages_from_scratch.html) や [.gitlab-ci.yml · 99a1d7fbb50c28d6eee87544db9779d185bd66b1 · GitLab Pages examples / hakyll · GitLab](https://gitlab.com/pages/hakyll/-/blob/99a1d7fbb50c28d6eee87544db9779d185bd66b1/.gitlab-ci.yml) を見るに、 `image` を使うのが一般的なようなので、 Docker Image を使うことにします。運が良く公式から Coq のための Docker Image が提供されているので、それを使います。

GitLab Pages の公開には job artifacts という機能を使います。これは、ジョブで生成したファイルを artifact という設定で指定して保存しておくことが出来るという機能です。これで `public/` というフォルダを保存しておくと、それが自動的に GitLab Pages に公開されます。 git でコミットする必要がある GitHub Pages と比べると、非常に簡単です。 [.gitlab-ci.yml · 8e50db79c284cd4a0f853b0859a96b976666198d · Hexirp Prixeh / googology-in-coq · GitLab](https://gitlab.com/Hexirp/googology-in-coq/-/blob/8e50db79c284cd4a0f853b0859a96b976666198d/.gitlab-ci.yml) と、 [blog/.travis.yml at 4af52051e85339aee8a62b539fbc31b1ab20aaf9 · Hexirp/blog](https://github.com/Hexirp/blog/blob/4af52051e85339aee8a62b539fbc31b1ab20aaf9/.travis.yml) と [blog/deploy.sh at 4af52051e85339aee8a62b539fbc31b1ab20aaf9 · Hexirp/blog](https://github.com/Hexirp/blog/blob/4af52051e85339aee8a62b539fbc31b1ab20aaf9/deploy.sh) を比べてみてください。簡単さが段違いです。
