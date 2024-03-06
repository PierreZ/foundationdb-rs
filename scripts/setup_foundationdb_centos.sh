#!/usr/bin/env bash

if [[ -z "${FDB_VERSION}" ]]; then
  echo "FDB_VERSION unset, exiting";
  exit 1;
fi

cd /tmp
echo "installing fdbclient..."
wget https://github.com/apple/foundationdb/releases/download/$FDB_VERSION/foundationdb-clients-$FDB_VERSION-1.el7.x86_64.rpm
rpm -i /tmp/foundationdb-clients-$FDB_VERSION-1.el7.x86_64.rpm

echo "installing fdbserver..."
wget https://github.com/apple/foundationdb/releases/download/$FDB_VERSION/foundationdb-server-$FDB_VERSION-1.el7.x86_64.rpm
rpm -i /tmp/foundationdb-server-$FDB_VERSION-1.el7.x86_64.rpm

echo "done!"