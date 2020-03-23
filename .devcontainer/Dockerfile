FROM python:3
WORKDIR ~
RUN curl https://raw.githubusercontent.com/Kha/elan/master/elan-init.sh -sSf | bash -s -- --default-toolchain none -y
RUN pip3 install mathlibtools
# sometimes it doesn't source ~/.profile so just put in the path manually.
ENV PATH $PATH:/root/.elan/bin
ENV LC_ALL C.UTF-8
ENV LANG C.UTF-8
RUN elan toolchain install leanprover-community/lean:3.6.1
CMD ["bash"]