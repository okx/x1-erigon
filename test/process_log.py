import re
import argparse
import logging
from datetime import datetime

# 配置日志记录
logging.basicConfig(level=logging.INFO, format='%(asctime)s - %(levelname)s - %(message)s')

def parse_time(line):
    # 假设时间戳在行的开头，格式为 [MM-DD|HH:MM:SS.SSS]
    match = re.search(r'\[(\d{2}-\d{2}\|\d{2}:\d{2}:\d{2}\.\d{3})\]', line)
    if match:
        return datetime.strptime(match.group(1), '%m-%d|%H:%M:%S.%f')
    return None

def main(log_file):
    last_batch = None
    highest_batch_in_data_stream = None
    start_time = None
    end_time = None
    tx_count = 0

    with open(log_file, 'r') as file:
        lines = file.readlines()

        if len(lines) < 5:
            logging.error("Log file does not contain enough lines.")
            return

        # 读取 lastBatch 和 highestBatchInDataStream
        last_batch = int(re.search(r'Last batch (\d+)', lines[0]).group(1))
        highest_batch_in_data_stream = int(re.search(r'Highest batch in data stream (\d+)', lines[1]).group(1))

        # 计算需要读取的批次数量
        batches_to_read = highest_batch_in_data_stream - last_batch

        # 找到 startTime
        for i, line in enumerate(lines):
            if f"Read {batches_to_read} batches from data stream" in line:
                start_time = parse_time(line)
                break

        if not start_time:
            logging.error("Start time not found.")
            return

        # 计算 txCount
        for line in lines[i:]:
            if "Finish block" in line:
                match = re.search(r'Finish block \d+ with (\d+) transactions', line)
                if match:
                    tx_count += int(match.group(1))
            if "Resequencing completed." in line:
                end_time = parse_time(line)
                break

        if not end_time:
            logging.error("End time not found.")
            return

        # 计算 TPS
        duration = (end_time - start_time).total_seconds()
        tps = tx_count / duration if duration > 0 else 0

        logging.info(f"{'Start Time:':<20} {start_time}")
        logging.info(f"{'End Time:':<20} {end_time}")
        logging.info(f"{'Total Transactions:':<20} {tx_count}")
        logging.info(f"{'Duration:':<20} {duration} seconds")
        logging.info(f"{'TPS:':<20} {tps}")

if __name__ == "__main__":
    parser = argparse.ArgumentParser(description='Process log file to calculate TPS.')
    parser.add_argument('log_file', type=str, help='Path to the log file')
    args = parser.parse_args()
    main(args.log_file)