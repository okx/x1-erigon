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

# global & shell env variables
USER_PREFIX = $(shell awk '/^user:/ {print $$2}' lrp.config.yaml)
IMAGE_TAG = $(USER_PREFIX)-$(shell git rev-parse --short HEAD)
export USER_PREFIX IMAGE_TAG
PORT_DIFF = $(shell awk '/^portDiff:/ {print $$2}' lrp.config.yaml)
PPROF_PORT = $(shell echo $$((6060 + $(PORT_DIFF))))
RPC_PORT = $(shell echo $$((8545 + $(PORT_DIFF))))
DS_PORT = $(shell echo $$((6900 + $(PORT_DIFF))))
METRICS_PORT = $(shell echo $$((9095 + $(PORT_DIFF))))
EXTERNAL_DS_PORT = $(shell echo $$((16900 + $(PORT_DIFF))))
export PPROF_PORT RPC_PORT DS_PORT METRICS_PORT EXTERNAL_DS_PORT

DOCKER_COMPOSE_LRP := docker compose -f docker-compose-lrp.yml -p $(USER_PREFIX)-xlayer-lrp
DOCKER_MAINNET_LRP_UNWIND := xlayer-mainnet-lrp-unwind
DOCKER_MAINNET_LRP_UNWIND_CONTAINER := $(USER_PREFIX)-xlayer-mainnet-lrp-unwind
DOCKER_MAINNET_LRP_RESEQUENCE := xlayer-mainnet-lrp-resequence
DOCKER_MAINNET_LRP_RESEQUENCE_WITH_EXTERNAL_DATASTREAM := xlayer-mainnet-lrp-resequence-with-external-datastream
DOCKER_MAINNET_LRP_RESEQUENCE_CONTAINER := $(USER_PREFIX)-xlayer-mainnet-lrp-resequence

RUN_DOCKER_LRP_STATELESS_EXECUTOR := $(DOCKER_COMPOSE_LRP) up -d $(DOCKER_STATELESS_EXECUTOR)
RUN_DOCKER_MAINNET_LRP_UNWIND := $(DOCKER_COMPOSE_LRP) up -d $(DOCKER_MAINNET_LRP_UNWIND)
RUN_DOCKER_MAINNET_LRP_RESEQUENCE := $(DOCKER_COMPOSE_LRP) --profile internal-ds up -d $(DOCKER_MAINNET_LRP_RESEQUENCE)
RUN_DOCKER_MAINNET_LRP_RESEQUENCE_WITH_EXTERNAL_DATASTREAM := $(DOCKER_COMPOSE_LRP) --profile external-ds up -d $(DOCKER_MAINNET_LRP_RESEQUENCE_WITH_EXTERNAL_DATASTREAM)

UNWIND_LOG_FILE := unwind.log
RESEQUENCE_LOG_FILE := resequence.log
RESEQUENCE_FILTERED_LOG_FILE := resequence_filtered.log
BLOCKHASHES_LOG_FILE := blockhashes.log

.PHONY: lrp-config
lrp-config:
	@read -p "Enter fromBatchNumber: " FROM_BATCH_NO; \
	read -p "Enter toBatchNumber: " TO_BATCH_NO; \
	read -p "Use external datastream? (y/n): " USE_EXTERNAL_DS; \
	read -p "Enter user: " USER_NAME; \
	if [ -z "$$USER_NAME" ]; then \
		USER_NAME=$$(if [ -n "$$SUDO_USER" ]; then echo "$$SUDO_USER"; else echo "$$USER"; fi); \
	fi; \
	read -p "Enter portDiff: " PORT_DIFF; \
	UNWIND_BATCH_NO=$$((FROM_BATCH_NO - 1)); \
	if [ "$$USE_EXTERNAL_DS" = "y" ]; then \
		EXTERNAL_DS="true"; \
	else \
		EXTERNAL_DS="false"; \
	fi; \
	if [ "$(shell uname)" = "Darwin" ]; then \
		sed -i '' "s/--unwind-batch-no=[0-9]*/--unwind-batch-no=$$UNWIND_BATCH_NO/" docker-compose-lrp.yml; \
		sed -i '' "s/--zkevm.sequencer-resequence-halt-on-batch-number=[0-9]*/--zkevm.sequencer-resequence-halt-on-batch-number=$$TO_BATCH_NO/" docker-compose-lrp.yml; \
		sed -i '' "s/--zkevm.sequencer-resequence-external-datastream=\(true\|false\)/--zkevm.sequencer-resequence-external-datastream=$$EXTERNAL_DS/" docker-compose-lrp.yml; \
	else \
		sed -i "s/--unwind-batch-no=[0-9]*/--unwind-batch-no=$$UNWIND_BATCH_NO/" docker-compose-lrp.yml; \
		sed -i "s/--zkevm.sequencer-resequence-halt-on-batch-number=[0-9]*/--zkevm.sequencer-resequence-halt-on-batch-number=$$TO_BATCH_NO/" docker-compose-lrp.yml; \
		sed -i "s/--zkevm.sequencer-resequence-external-datastream=\(true\|false\)/--zkevm.sequencer-resequence-external-datastream=$$EXTERNAL_DS/" docker-compose-lrp.yml; \
	fi; \
	if [ ! -f lrp.config.yaml ]; then \
		echo "fromBatchNumber: $$FROM_BATCH_NO" > lrp.config.yaml; \
		echo "toBatchNumber: $$TO_BATCH_NO" >> lrp.config.yaml; \
		echo "useExternalDatastream: $$EXTERNAL_DS" >> lrp.config.yaml; \
		echo "user: $$USER_NAME" >> lrp.config.yaml; \
		echo "portDiff: $$PORT_DIFF" >> lrp.config.yaml; \
	else \
		if [ "$(shell uname)" = "Darwin" ]; then \
			sed -i '' "s/^fromBatchNumber:.*/fromBatchNumber: $$FROM_BATCH_NO/" lrp.config.yaml; \
			sed -i '' "s/^toBatchNumber:.*/toBatchNumber: $$TO_BATCH_NO/" lrp.config.yaml; \
			sed -i '' "s/^useExternalDatastream:.*/useExternalDatastream: $$EXTERNAL_DS/" lrp.config.yaml; \
			sed -i '' "s/^user:.*/user: $$USER_NAME/" lrp.config.yaml; \
			sed -i '' "s/^portDiff:.*/portDiff: $$PORT_DIFF/" lrp.config.yaml; \
			if ! grep -q "^fromBatchNumber:" lrp.config.yaml; then echo "fromBatchNumber: $$FROM_BATCH_NO" >> lrp.config.yaml; fi; \
			if ! grep -q "^toBatchNumber:" lrp.config.yaml; then echo "toBatchNumber: $$TO_BATCH_NO" >> lrp.config.yaml; fi; \
			if ! grep -q "^useExternalDatastream:" lrp.config.yaml; then echo "useExternalDatastream: $$EXTERNAL_DS" >> lrp.config.yaml; fi; \
			if ! grep -q "^user:" lrp.config.yaml; then echo "user: $$USER_NAME" >> lrp.config.yaml; fi; \
			if ! grep -q "^portDiff:" lrp.config.yaml; then echo "portDiff: $$PORT_DIFF" >> lrp.config.yaml; fi; \
		else \
			sed -i "s/^fromBatchNumber:.*/fromBatchNumber: $$FROM_BATCH_NO/" lrp.config.yaml; \
			sed -i "s/^toBatchNumber:.*/toBatchNumber: $$TO_BATCH_NO/" lrp.config.yaml; \
			sed -i "s/^useExternalDatastream:.*/useExternalDatastream: $$EXTERNAL_DS/" lrp.config.yaml; \
			sed -i "s/^user:.*/user: $$USER_NAME/" lrp.config.yaml; \
			sed -i "s/^portDiff:.*/portDiff: $$PORT_DIFF/" lrp.config.yaml; \
			if ! grep -q "^fromBatchNumber:" lrp.config.yaml; then echo "fromBatchNumber: $$FROM_BATCH_NO" >> lrp.config.yaml; fi; \
			if ! grep -q "^toBatchNumber:" lrp.config.yaml; then echo "toBatchNumber: $$TO_BATCH_NO" >> lrp.config.yaml; fi; \
			if ! grep -q "^useExternalDatastream:" lrp.config.yaml; then echo "useExternalDatastream: $$EXTERNAL_DS" >> lrp.config.yaml; fi; \
			if ! grep -q "^user:" lrp.config.yaml; then echo "user: $$USER_NAME" >> lrp.config.yaml; fi; \
			if ! grep -q "^portDiff:" lrp.config.yaml; then echo "portDiff: $$PORT_DIFF" >> lrp.config.yaml; fi; \
		fi; \
	fi

.PHONY: lrp-config-apply
lrp-config-apply:
	@FROM_BATCH_NO=$$(awk '/^fromBatchNumber:/ {print $$2}' lrp.config.yaml); \
	TO_BATCH_NO=$$(awk '/^toBatchNumber:/ {print $$2}' lrp.config.yaml); \
	EXTERNAL_DS=$$(awk '/^useExternalDatastream:/ {print $$2}' lrp.config.yaml); \
	UNWIND_BATCH_NO=$$((FROM_BATCH_NO - 1)); \
	if [ "$(shell uname)" = "Darwin" ]; then \
		sed -i '' "s/--unwind-batch-no=[0-9]*/--unwind-batch-no=$$UNWIND_BATCH_NO/" docker-compose-lrp.yml; \
		sed -i '' "s/--zkevm.sequencer-resequence-halt-on-batch-number=[0-9]*/--zkevm.sequencer-resequence-halt-on-batch-number=$$TO_BATCH_NO/" docker-compose-lrp.yml; \
		sed -i '' "s/--zkevm.sequencer-resequence-external-datastream=\(true\|false\)/--zkevm.sequencer-resequence-external-datastream=$$EXTERNAL_DS/" docker-compose-lrp.yml; \
	else \
		sed -i "s/--unwind-batch-no=[0-9]*/--unwind-batch-no=$$UNWIND_BATCH_NO/" docker-compose-lrp.yml; \
		sed -i "s/--zkevm.sequencer-resequence-halt-on-batch-number=[0-9]*/--zkevm.sequencer-resequence-halt-on-batch-number=$$TO_BATCH_NO/" docker-compose-lrp.yml; \
		sed -i "s/--zkevm.sequencer-resequence-external-datastream=\(true\|false\)/--zkevm.sequencer-resequence-external-datastream=$$EXTERNAL_DS/" docker-compose-lrp.yml; \
	fi

.PHONY: lrp-build-docker
lrp-build-docker: # Build cdk-erigoin for lrp
	@docker build -t cdk-erigon:$(IMAGE_TAG) -f ../Dockerfile.local ../

.PHONY: lrp-mainnet
lrp-mainnet: lrp-config-apply lrp-build-docker
	$(RUN_DOCKER_MAINNET_LRP_UNWIND)
	@docker wait $(DOCKER_MAINNET_LRP_UNWIND_CONTAINER); \
	docker logs $(DOCKER_MAINNET_LRP_UNWIND_CONTAINER) > $(UNWIND_LOG_FILE) 2>&1
	@# $(RUN_DOCKER_LRP_STATELESS_EXECUTOR)
	@# sleep 3
	@EXTERNAL_DS=$$(awk '/^useExternalDatastream:/ {print $$2}' lrp.config.yaml); \
	if [ "$$EXTERNAL_DS" = "true" ]; then \
		$(RUN_DOCKER_MAINNET_LRP_RESEQUENCE_WITH_EXTERNAL_DATASTREAM); \
	else \
		$(RUN_DOCKER_MAINNET_LRP_RESEQUENCE); \
	fi

.PHONY: lrp-mainnet-unwind
lrp-mainnet-unwind: lrp-config-apply lrp-build-docker
	$(RUN_DOCKER_MAINNET_LRP_UNWIND)
	@docker wait $(DOCKER_MAINNET_LRP_UNWIND_CONTAINER); \
	docker logs $(DOCKER_MAINNET_LRP_UNWIND_CONTAINER) > $(UNWIND_LOG_FILE) 2>&1

.PHONY: lrp-mainnet-resequence
lrp-mainnet-resequence: lrp-config-apply lrp-build-docker
	@# $(RUN_DOCKER_LRP_STATELESS_EXECUTOR)
	@# sleep 3
	@EXTERNAL_DS=$$(awk '/^useExternalDatastream:/ {print $$2}' lrp.config.yaml); \
	if [ "$$EXTERNAL_DS" = "true" ]; then \
		$(RUN_DOCKER_MAINNET_LRP_RESEQUENCE_WITH_EXTERNAL_DATASTREAM); \
	else \
		$(RUN_DOCKER_MAINNET_LRP_RESEQUENCE); \
	fi

.PHONY: lrp-mainnet-resequence-pause
lrp-mainnet-resequence-pause:
	@EXTERNAL_DS=$$(awk '/^useExternalDatastream:/ {print $$2}' lrp.config.yaml); \
	if [ "$$EXTERNAL_DS" = "true" ]; then \
		docker stop $(DOCKER_MAINNET_LRP_RESEQUENCE_CONTAINER) --time 600; \
	else \
		echo "Warning: useExternalDatastream is set to false, batches data will be lost"; \
	fi

.PHONY: lrp-mainnet-data-refresh
lrp-mainnet-data-refresh:
	@SRC_PATH=$$(awk '/^srcMainnetDataPath:/ {print $$2}' lrp.config.yaml); \
	if [ -z "$$SRC_PATH" ]; then \
		echo "Error: srcMainnetDataPath not found in lrp.config.yaml"; \
		echo "Please add 'srcMainnetDataPath: /path/to/mainnet/data' to lrp.config.yaml"; \
		exit 1; \
	fi; \
	EXPANDED_PATH=$$(echo "$$SRC_PATH" | envsubst); \
	if [ ! -d "$$EXPANDED_PATH" ]; then \
		echo "Error: Source directory $$EXPANDED_PATH does not exist"; \
		exit 1; \
	fi; \
	mkdir -p mainnet; \
	rm -rf mainnet/seq; \
	cp -r "$$EXPANDED_PATH" mainnet/seq

.PHONY: lrp-mainnet-data-compact
lrp-mainnet-data-compact:
	@if [ ! -f ./mainnet/seq/chaindata/mdbx.dat ]; then \
		echo "Error: Database file not found at ./mainnet/seq/chaindata/mdbx.dat"; \
		exit 1; \
	fi; \
	mkdir -p tmp; \
	echo "Compacting database file..."; \
	../build/bin/mdbx_copy -c ./mainnet/seq/chaindata/mdbx.dat ./tmp/mdbx.dat; \
	if [ $$? -eq 0 ]; then \
		echo "Replacing original database file with compacted version..."; \
		mv ./mainnet/seq/chaindata/mdbx.dat ./mainnet/seq/chaindata/mdbx.dat.bak; \
		mv ./tmp/mdbx.dat ./mainnet/seq/chaindata/mdbx.dat; \
		rm -f ./mainnet/seq/chaindata/mdbx.dat.bak; \
		rm -rf tmp; \
		echo "Database compaction completed successfully."; \
	else \
		echo "Error: Database compaction failed"; \
		rm -rf tmp; \
		exit 1; \
	fi

.PHONY: lrp-mainnet-tps
lrp-mainnet-tps: # Filter logs for LRP & Compute TPS
	@docker logs $(DOCKER_MAINNET_LRP_RESEQUENCE_CONTAINER) > $(RESEQUENCE_LOG_FILE) 2>&1; \
	docker logs $(DOCKER_MAINNET_LRP_RESEQUENCE_CONTAINER) 2>&1 | grep "\[5/13 Execution\]" > $(RESEQUENCE_FILTERED_LOG_FILE); \
	python process_log.py $(RESEQUENCE_FILTERED_LOG_FILE)

.PHONY: lrp-stop
lrp-stop:
	@docker ps -a | grep "$(USER_PREFIX)-xlayer" | cut -d' ' -f1 | xargs -r docker stop; \
	docker ps -a | grep "$(USER_PREFIX)-xlayer" | cut -d' ' -f1 | xargs -r docker rm -f; \
	docker network rm $(USER_PREFIX)-erigon-lrp 2>/dev/null || true
