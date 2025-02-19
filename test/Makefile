DOCKER_COMPOSE := docker compose -f docker-compose.yml
DOCKER_STATELESS_EXECUTOR := xlayer-executor
DOCKER_SEQ_SENDER := xlayer-seqs
DOCKER_AGGREGATOR := xlayer-agg
DOCKER_AGGREGATOR_DB := xlayer-agg-db
DOCKER_BRIDGE_DB := xlayer-bridge-db
DOCKER_BRIDGE_REDIS := xlayer-bridge-redis
DOCKER_BRIDGE_ZOOKEEPER := kafka-zookeeper
DOCKER_BRIDGE_COIN_KAFKA := xlayer-bridge-coin-kafka
DOCKER_BRIDGE_SERVICE := xlayer-bridge-service
DOCKER_BRIDGE_UI := xlayer-bridge-ui
DOCKER_PROVER := xlayer-prover
DOCKER_APPROVE := xlayer-approve
DOCKER_SEQ := xlayer-seq
DOCKER_RPC := xlayer-rpc
DOCKER_L1_NETWORK := xlayer-mock-l1-network
DOCKER_DATA_AVAILABILITY := xlayer-da
DOCKER_DATA_AVAILABILITY_DB := xlayer-da-db
DOCKER_POOL_DB := xlayer-pool-db
DOCKER_POOL_MANAGER := xlayer-pool-manager
DOCKER_SIGNER := xlayer-signer
DOCKER_DS := xlayer-ds
DOCKER_PROMETHEUS := prometheus
DOCKER_GRAFANA := grafana
DOCKER_MAINNET_SEQ := xlayer-mainnet-seq

RUN_DOCKER_STATELESS_EXECUTOR := $(DOCKER_COMPOSE) up -d $(DOCKER_STATELESS_EXECUTOR)
RUN_DOCKER_SEQ_SENDER := $(DOCKER_COMPOSE) up -d $(DOCKER_SEQ_SENDER)
RUN_DOCKER_AGGREGATOR := $(DOCKER_COMPOSE) up -d $(DOCKER_AGGREGATOR)
RUN_DOCKER_AGGREGATOR_DB := $(DOCKER_COMPOSE) up -d $(DOCKER_AGGREGATOR_DB)
RUN_DOCKER_BRIDGE_DB := $(DOCKER_COMPOSE) up -d $(DOCKER_BRIDGE_DB)
RUN_DOCKER_BRIDGE_REDIS := $(DOCKER_COMPOSE) up -d $(DOCKER_BRIDGE_REDIS)
RUN_DOCKER_BRIDGE_ZOOKEEPER := $(DOCKER_COMPOSE) up -d $(DOCKER_BRIDGE_ZOOKEEPER)
RUN_DOCKER_BRIDGE_COIN_KAFKA := $(DOCKER_COMPOSE) up -d $(DOCKER_BRIDGE_COIN_KAFKA)
RUN_DOCKER_BRIDGE_SERVICE := $(DOCKER_COMPOSE) up -d $(DOCKER_BRIDGE_SERVICE)
RUN_DOCKER_BRIDGE_UI := $(DOCKER_COMPOSE) up -d $(DOCKER_BRIDGE_UI)
RUN_DOCKER_PROVER := $(DOCKER_COMPOSE) up -d $(DOCKER_PROVER)
RUN_DOCKER_APPROVE := $(DOCKER_COMPOSE) up -d $(DOCKER_APPROVE)
RUN_DOCKER_SEQ := $(DOCKER_COMPOSE) up -d $(DOCKER_SEQ)
RUN_DOCKER_RPC := $(DOCKER_COMPOSE) up -d $(DOCKER_RPC)
RUN_DOCKER_MAINNET_SEQ := $(DOCKER_COMPOSE) up -d $(DOCKER_MAINNET_SEQ)
RUN_DOCKER_L1_NETWORK := $(DOCKER_COMPOSE) up -d $(DOCKER_L1_NETWORK)
RUN_DOCKER_DATA_AVAILABILITY := $(DOCKER_COMPOSE) up -d $(DOCKER_DATA_AVAILABILITY)
RUN_DOCKER_DATA_AVAILABILITY_DB := $(DOCKER_COMPOSE) up -d $(DOCKER_DATA_AVAILABILITY_DB)
RUN_DOCKER_POOL_DB := $(DOCKER_COMPOSE) up -d $(DOCKER_POOL_DB)
RUN_DOCKER_POOL_MANAGER := $(DOCKER_COMPOSE) up -d $(DOCKER_POOL_MANAGER)
RUN_DOCKER_SIGNER := $(DOCKER_COMPOSE) up -d $(DOCKER_SIGNER)
RUN_DOCKER_DS := $(DOCKER_COMPOSE) up -d $(DOCKER_DS)
RUN_DOCKER_PROMETHEUS := $(DOCKER_COMPOSE) up -d $(DOCKER_PROMETHEUS)
RUN_DOCKER_GRAFANA := $(DOCKER_COMPOSE) up -d $(DOCKER_GRAFANA)

STOP := $(DOCKER_COMPOSE) down --remove-orphans; sleep 3; rm -rf data

.PHONY: build-docker
build-docker: ## Build cdk-erigoin for sequencer and rpc
	docker build -t cdk-erigon -f ../Dockerfile.local ../

.PHONY: run
run: build-docker ## Runs a full node
	# base services
	$(RUN_DOCKER_L1_NETWORK)
	$(RUN_DOCKER_DATA_AVAILABILITY_DB)
	$(RUN_DOCKER_POOL_DB)
	$(RUN_DOCKER_AGGREGATOR_DB)
	sleep 3
	$(RUN_DOCKER_DATA_AVAILABILITY)
	$(RUN_DOCKER_APPROVE)
	$(RUN_DOCKER_STATELESS_EXECUTOR)

	# app services
	sleep 3
	$(RUN_DOCKER_SEQ)
	$(RUN_DOCKER_PROVER)
	sleep 10
	$(RUN_DOCKER_DS)
	$(RUN_DOCKER_SIGNER)
	$(RUN_DOCKER_SEQ_SENDER)
	$(RUN_DOCKER_AGGREGATOR)
	$(RUN_DOCKER_POOL_MANAGER)
	$(RUN_DOCKER_RPC)

	# monitoring services
	$(RUN_DOCKER_PROMETHEUS)
	$(RUN_DOCKER_GRAFANA)

.PHONY: all
all: build-docker ## Runs a full node
	# base services
	$(RUN_DOCKER_L1_NETWORK)
	$(RUN_DOCKER_DATA_AVAILABILITY_DB)
	$(RUN_DOCKER_POOL_DB)
	$(RUN_DOCKER_AGGREGATOR_DB)
	$(RUN_DOCKER_BRIDGE_DB)
	$(RUN_DOCKER_BRIDGE_REDIS)
	$(RUN_DOCKER_BRIDGE_ZOOKEEPER)
	$(RUN_DOCKER_BRIDGE_COIN_KAFKA)
	sleep 3
	$(RUN_DOCKER_DATA_AVAILABILITY)
	$(RUN_DOCKER_APPROVE)
	$(RUN_DOCKER_STATELESS_EXECUTOR)

	# app services
	sleep 3
	$(RUN_DOCKER_SEQ)
	$(RUN_DOCKER_PROVER)
	sleep 10
	$(RUN_DOCKER_DS)
	$(RUN_DOCKER_SIGNER)
	$(RUN_DOCKER_SEQ_SENDER)
	$(RUN_DOCKER_AGGREGATOR)
	$(RUN_DOCKER_POOL_MANAGER)
	$(RUN_DOCKER_RPC)

	# bridge services
	sleep 30
	$(RUN_DOCKER_BRIDGE_SERVICE)
	sleep 3
	$(RUN_DOCKER_BRIDGE_UI)

	# monitoring services
	$(RUN_DOCKER_PROMETHEUS)
	$(RUN_DOCKER_GRAFANA)

.PHONY: stop
stop: ## Stops all services
	$(STOP)

.PHONY: min-run
min-run: build-docker ## Runs a minimal node
	$(RUN_DOCKER_L1_NETWORK)
	$(RUN_DOCKER_STATELESS_EXECUTOR)
	sleep 10
	$(RUN_DOCKER_SEQ)
	sleep 10
	$(RUN_DOCKER_DS)
	sleep 10
	$(RUN_DOCKER_RPC)

.PHONY: test
test: test-1 ## Runs all e2e tests
	echo "Tests passed"
	sleep 3

.PHONY: test-1
test-1: stop all ## Runs group 1 e2e tests checking race conditions
	sleep 3
	docker ps -a
	trap '$(STOP)' EXIT; MallocNanoZone=0 go test -count=1 -failfast -race -v -p 1 -timeout 600s ../ci/e2e-1/...

mainnet: build-docker
	# base services
	$(RUN_DOCKER_MAINNET_SEQ)
	# monitoring services
	$(RUN_DOCKER_PROMETHEUS)
	$(RUN_DOCKER_GRAFANA)

DOCKER_COMPOSE_LRP := docker compose -f docker-compose-lrp.yml
DOCKER_LRP_UNWIND := xlayer-lrp-unwind
DOCKER_LRP_RESEQUENCE := xlayer-lrp-resequence
DOCKER_MAINNET_LRP_UNWIND := xlayer-mainnet-lrp-unwind
DOCKER_MAINNET_LRP_RESEQUENCE := xlayer-mainnet-lrp-resequence
DOCKER_MAINNET_LRP_RESEQUENCE_WITH_EXTERNAL_DATASTREAM := xlayer-mainnet-lrp-resequence-with-external-datastream

RUN_DOCKER_LRP_STATELESS_EXECUTOR := $(DOCKER_COMPOSE_LRP) up -d $(DOCKER_STATELESS_EXECUTOR)
RUN_DOCKER_LRP_L1_NETWORK := $(DOCKER_COMPOSE_LRP) up -d $(DOCKER_L1_NETWORK)
RUN_DOCKER_LRP_UNWIND := $(DOCKER_COMPOSE_LRP) up -d $(DOCKER_LRP_UNWIND)
RUN_DOCKER_LRP_RESEQUENCE := $(DOCKER_COMPOSE_LRP) up -d $(DOCKER_LRP_RESEQUENCE)
RUN_DOCKER_MAINNET_LRP_UNWIND := $(DOCKER_COMPOSE_LRP) up -d $(DOCKER_MAINNET_LRP_UNWIND)
RUN_DOCKER_MAINNET_LRP_RESEQUENCE := $(DOCKER_COMPOSE_LRP) up -d $(DOCKER_MAINNET_LRP_RESEQUENCE)
RUN_DOCKER_MAINNET_LRP_RESEQUENCE_WITH_EXTERNAL_DATASTREAM := $(DOCKER_COMPOSE_LRP) up -d $(DOCKER_MAINNET_LRP_RESEQUENCE_WITH_EXTERNAL_DATASTREAM)

STOP_LRP := $(DOCKER_COMPOSE_LRP) down --remove-orphans; sleep 3; rm -rf data

UNWIND_LOG_FILE := unwind.log
RESEQUENCE_LOG_FILE := resequence.log
RESEQUENCE_FILTERED_LOG_FILE := resequence_filtered.log
BLOCKHASHES_LOG_FILE := blockhashes.log

.PHONY: configure-lrp
configure-lrp:
	@read -p "Enter fromBatchNumber: " FROM_BATCH_NO; \
	read -p "Enter toBatchNumber: " TO_BATCH_NO; \
	UNWIND_BATCH_NO=$$((FROM_BATCH_NO - 1)); \
	if [ "$(shell uname)" = "Darwin" ]; then \
		sed -i '' "s/--unwind-batch-no=[0-9]*/--unwind-batch-no=$$UNWIND_BATCH_NO/" docker-compose-lrp.yml; \
		sed -i '' "s/--zkevm.sequencer-resequence-halt-on-batch-number=[0-9]*/--zkevm.sequencer-resequence-halt-on-batch-number=$$TO_BATCH_NO/" docker-compose-lrp.yml; \
	else \
		sed -i "s/--unwind-batch-no=[0-9]*/--unwind-batch-no=$$UNWIND_BATCH_NO/" docker-compose-lrp.yml; \
		sed -i "s/--zkevm.sequencer-resequence-halt-on-batch-number=[0-9]*/--zkevm.sequencer-resequence-halt-on-batch-number=$$TO_BATCH_NO/" docker-compose-lrp.yml; \
	fi

.PHONY: lrp-run
lrp-run: build-docker configure-lrp
	$(RUN_DOCKER_LRP_L1_NETWORK)
	sleep 3
	$(RUN_DOCKER_LRP_UNWIND)
	docker wait $(DOCKER_LRP_UNWIND)
	docker logs $(DOCKER_LRP_UNWIND) > $(UNWIND_LOG_FILE) 2>&1
	$(RUN_DOCKER_LRP_RESEQUENCE)

.PHONY: lrp-check
lrp-check: ## Filter logs for LRP & Compute TPS & Check stateroots (configure debugToolsConfig.yaml)
	docker logs $(DOCKER_LRP_RESEQUENCE) > $(RESEQUENCE_LOG_FILE) 2>&1
	docker logs $(DOCKER_LRP_RESEQUENCE) 2>&1 | grep "\[5/13 Execution\]" > $(RESEQUENCE_FILTERED_LOG_FILE)
	python process_log.py $(RESEQUENCE_FILTERED_LOG_FILE)
	go run ../zk/debug_tools/rpc-blockhashes-compare/main.go

.PHONY: lrp-mainnet
lrp-mainnet: build-docker configure-lrp
	$(RUN_DOCKER_MAINNET_LRP_UNWIND)
	docker wait $(DOCKER_MAINNET_LRP_UNWIND)
	docker logs $(DOCKER_MAINNET_LRP_UNWIND) > $(UNWIND_LOG_FILE) 2>&1
	# $(RUN_DOCKER_LRP_STATELESS_EXECUTOR)
	# sleep 3
	$(RUN_DOCKER_MAINNET_LRP_RESEQUENCE)

.PHONY: lrp-mainnet-unwind
lrp-mainnet-unwind: build-docker configure-lrp
	$(RUN_DOCKER_MAINNET_LRP_UNWIND)
	docker wait $(DOCKER_MAINNET_LRP_UNWIND)
	docker logs $(DOCKER_MAINNET_LRP_UNWIND) > $(UNWIND_LOG_FILE) 2>&1

.PHONY: lrp-mainnet-post-unwind
lrp-mainnet-post-unwind: build-docker
	# $(RUN_DOCKER_LRP_STATELESS_EXECUTOR)
	# sleep 3
	$(RUN_DOCKER_MAINNET_LRP_RESEQUENCE)

.PHONY: lrp-mainnet-resequence-with-external-ds
lrp-mainnet-resequence-with-external-ds: build-docker
	$(RUN_DOCKER_MAINNET_LRP_RESEQUENCE_WITH_EXTERNAL_DATASTREAM)

.PHONY: lrp-mainnet-check
lrp-mainnet-check: ## Filter logs for LRP & Compute TPS & Check stateroots (configure debugToolsConfig.yaml)
	docker logs $(DOCKER_MAINNET_LRP_RESEQUENCE) > $(RESEQUENCE_LOG_FILE) 2>&1
	docker logs $(DOCKER_MAINNET_LRP_RESEQUENCE) 2>&1 | grep "\[5/13 Execution\]" > $(RESEQUENCE_FILTERED_LOG_FILE)
	python process_log.py $(RESEQUENCE_FILTERED_LOG_FILE)
	go run ../zk/debug_tools/rpc-blockhashes-compare/main.go

.PHONY: watch-blockhashes
watch-blockhashes:
	watch -n 300 'echo "\n[$(shell date "+%Y-%m-%d %H:%M:%S")]" >> $(BLOCKHASHES_LOG_FILE) && go run ../zk/debug_tools/rpc-blockhashes-compare/main.go | tee -a $(BLOCKHASHES_LOG_FILE)'

.PHONY: lrp-stop
lrp-stop:
	$(STOP_LRP)
