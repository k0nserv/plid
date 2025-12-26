FROM rust:1.92-trixie

RUN apt-get update && apt-get install -y \
  valgrind\ 
  libclang-dev\
  build-essential\
  libreadline-dev\
  zlib1g-dev\
  flex\
  bison\
  libxml2-dev\
  libxslt-dev\
  libssl-dev\
  libxml2-utils\
  xsltproc\
  ccache\
  pkg-config

RUN useradd -m postgres
USER postgres

RUN cargo install --locked cargo-pgrx
RUN cargo pgrx init --valgrind

