#!/bin/bash
set -e

SOURCE_FILE="/Users/jasonhuang/Downloads/mainnet.tar.gz"
POD_NAME="erigon-seq-687ff67-5sfv2"
DEST_PATH="/data"
CHUNK_SIZE="1G"

# Get the starting part number from command line argument
START_PART=${1:-0}  # Default to 0 if no argument provided

# Check if parts already exist
if ! ls "${SOURCE_FILE}.part_"* >/dev/null 2>&1; then
    echo "Splitting file..."
    split -b $CHUNK_SIZE -d "$SOURCE_FILE" "${SOURCE_FILE}.part_"
else
    echo "Parts already exist, skipping split..."
fi

echo "Transferring parts starting from part_${START_PART}..."
for part in "${SOURCE_FILE}.part_"[0-9][0-9]; do
    part_num=$(basename "$part" | grep -o '[0-9]\+$')
    if [ "$part_num" -lt "$START_PART" ]; then
        echo "Skipping $part..."
        continue
    fi
    echo "Transferring $part..."
    filename=$(basename "$part")
    ./krsync.sh -v --progress --stats --checksum "$part" "$POD_NAME:$DEST_PATH/$filename"
done


echo "Reassembling file in pod..."
SOURCE_FILENAME=$(basename "$SOURCE_FILE")
kubectl exec "$POD_NAME" -- bash -c "cd $DEST_PATH && cat ${SOURCE_FILENAME}.part_* > $SOURCE_FILENAME"

echo "Verifying checksum..."
DEST_CHECKSUM=$(kubectl exec "$POD_NAME" -- bash -c "cd $DEST_PATH && shasum -a 256 $SOURCE_FILENAME" | awk '{print $1}')

echo "Calculating source file checksum..."
SOURCE_CHECKSUM=$(shasum -a 256 "$SOURCE_FILE" | awk '{print $1}')

if [ "$SOURCE_CHECKSUM" = "$DEST_CHECKSUM" ]; then
    echo "Checksum verification successful!"
else
    echo "Checksum verification failed!"
    echo "Source checksum: $SOURCE_CHECKSUM"
    echo "Destination checksum: $DEST_CHECKSUM"
    exit 1
fi

echo "Cleaning up local parts..."
rm "${SOURCE_FILE}.part_"*

echo "Done!" 