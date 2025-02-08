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
        current_year = datetime.now().year
        parsed_time = datetime.strptime(match.group(1), '%m-%d|%H:%M:%S.%f')
        return parsed_time.replace(year=current_year)
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
        # highest_batch_in_data_stream = int(re.search(r'highest batch in datastream (\d+)', lines[0]).group(1))
        halt_batch = int(re.search(r'resequencing from batch \d+ to (\d+)', lines[0]).group(1))

        # 计算启动时间
        first_line_time = parse_time(lines[0])
        second_line_time = parse_time(lines[1])
        startup_duration = (second_line_time - first_line_time).total_seconds()

        # 找到 startTime
        for i, line in enumerate(lines):
            if "Resequence from batch" in line and "in data stream" in line:
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

        logging.info(f"{'From Batch:':<25} {last_batch+1}")
        logging.info(f"{'To Batch:':<25} {halt_batch}")
        logging.info(f"{'Data Stream Startup:':<25} {startup_duration} seconds")
        logging.info(f"{'Start Time:':<25} {start_time}")
        logging.info(f"{'End Time:':<25} {end_time}")
        logging.info(f"{'Total Transactions:':<25} {tx_count}")
        logging.info(f"{'Re-sequencing Duration:':<25} {duration} seconds")
        logging.info(f"{'TPS:':<25} {tps}")

if __name__ == "__main__":
    parser = argparse.ArgumentParser(description='Process log file to calculate TPS.')
    parser.add_argument('log_file', type=str, help='Path to the log file')
    args = parser.parse_args()
    main(args.log_file)