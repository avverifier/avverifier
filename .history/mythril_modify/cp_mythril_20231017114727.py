import json
import time
import web3
from web3 import Web3
from mythril.analysis.symbolic import SymExecWrapper
from mythril.laser.ethereum.state.account import Account
from mythril.solidity.soliditycontract import EVMContract
from mythril.laser.ethereum.svm import LaserEVM
from mythril.analysis.module.modules import external_calls
from mythril.analysis.module import ModuleLoader
from check_storage import StorageCheck
import requests

def get_contract_creations(contract_addresses, api_key, retries=10, backoff_factor=0.3):
    url = "https://api.etherscan.io/api"
    params = {
        "module": "contract",
        "action": "getcontractcreation",
        "contractaddresses": contract_addresses,
        "apikey": api_key,
    }
    
    for _ in range(retries):
        try:
            response = requests.get(url, params=params)
            data = response.json()
            if data['status'] == "1":
                return data['result'][0]['txHash']
            else:
                print(f"Error getting contract creation: {data['message']}")
        except requests.exceptions.RequestException as e:
            print(f"Request failed: {e}")
        
        print(f"Retrying in {backoff_factor} seconds...")
        time.sleep(backoff_factor)

    return None

def get_contract_code(w3, contract_address):
    api_key = 'ur etherscan api'
    hash = get_contract_creations(contract_address, api_key)
    try:
        code = w3.eth.getTransaction(hash).get('input', None)
        return code
    except Exception as e:
        with open("error_log.txt", "a") as f:
            f.write(f"Error getting code for address {contract_address}: {str(e)}\n")
        return None

def analyze_contract(bytecode, address):
    try:
        contract = EVMContract(creation_code=bytecode)
        modules = ['StorageCheck']
        moduler = ModuleLoader()
        moduler.register_module(StorageCheck())
        wrapper = SymExecWrapper(
            contract = contract,
            address = address,
            strategy = 'dfs',
            max_depth = float('inf'),
            execution_timeout = 120,
            create_timeout = 120,
            modules = modules,
            module_loader = moduler,
            loop_bound=3
        )
        return wrapper.laser.issue_list
    except Exception as e:
        with open("error_log.txt", "a") as f:
            f.write(f"Error analyzing contract at address {address}: {str(e)}\n")
        return []

def main():
    w3 = Web3(Web3.HTTPProvider('https://eth.llamarpc.com'))

    with open("ca_open.txt", 'r') as f:
        contract_addresses = [line.strip() for line in f]

    for i, contract_address in enumerate(contract_addresses):
        try:
            contract_address = Web3.toChecksumAddress(contract_address)
            bytecode = get_contract_code(w3, contract_address)
            if bytecode is None:
                continue
            
            start_time = time.time()
            issue_list = analyze_contract(bytecode, contract_address)
            end_time = time.time()
            execution_time = end_time - start_time

            if len(issue_list) == 0:
                result = f"{i}. Contract address: {contract_address}\n\tNo vulnerable point!\n\tExecution time: {execution_time} seconds\n"
            else:
                for issue in issue_list:
                    result = (
                        f"{i}. Contract address: {contract_address}\n"
                        f"\tFunction: {issue.function_name}\n"
                        f"\tExecution time: {execution_time} seconds\n"
                    )
            with open("results.txt", 'a') as f:
                f.write(result + "----------------------------------------\n")
        except Exception as e:
            with open("error_log.txt", "a") as f:
                f.write(f"Error in main loop for address {contract_address}: {str(e)}\n")

if __name__ == "__main__":
    main()
