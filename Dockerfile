FROM debian:stretch
RUN apt-get update -qq && apt-get install -qy haskell-stack zlib1g-dev
RUN mkdir -p /app
WORKDIR /app
COPY stack* /app/
RUN stack setup
COPY pandoc.cabal /app/
RUN stack install --only-dependencies
COPY . /app
RUN stack install --flag pandoc:embed_data_files
ENV PATH="/root/.local/bin:${PATH}"
ENTRYPOINT ["/root/.local/bin/pandoc"]
