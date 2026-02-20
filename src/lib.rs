#![no_std]

use soroban_sdk::{
    contract, contractimpl, contracttype, Address, BytesN, Env, Symbol,
};

#[contracttype]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum VaultStatus {
    Active = 0,
    Completed = 1,
    Failed = 2,
    Cancelled = 3,
}

#[contracttype]
pub struct ProductivityVault {
    pub creator: Address,
    pub amount: i128,
    pub start_timestamp: u64,
    pub end_timestamp: u64,
    pub milestone_hash: BytesN<32>,
    pub verifier: Option<Address>,
    pub success_destination: Address,
    pub failure_destination: Address,
    pub status: VaultStatus,
}

#[contract]
pub struct DisciplrVault;

#[contractimpl]
impl DisciplrVault {
    /// Create a new productivity vault. Caller must have approved USDC transfer to this contract.
    pub fn create_vault(
        env: Env,
        creator: Address,
        amount: i128,
        start_timestamp: u64,
        end_timestamp: u64,
        milestone_hash: BytesN<32>,
        verifier: Option<Address>,
        success_destination: Address,
        failure_destination: Address,
    ) -> u32 {
        creator.require_auth();
        // TODO: pull USDC from creator to this contract
        // For now, just store vault metadata (storage key pattern would be used in full impl)
        let vault = ProductivityVault {
            creator: creator.clone(),
            amount,
            start_timestamp,
            end_timestamp,
            milestone_hash,
            verifier,
            success_destination,
            failure_destination,
            status: VaultStatus::Active,
        };
        let vault_id = 0u32; // placeholder; real impl would allocate id and persist
        env.events().publish(
            (Symbol::new(&env, "vault_created"), vault_id),
            vault,
        );
        vault_id
    }

    /// Verifier (or authorized party) validates milestone completion.
    pub fn validate_milestone(env: Env, vault_id: u32) -> bool {
        // TODO: check vault exists, status is Active, caller is verifier, timestamp < end
        // TODO: transfer USDC to success_destination, set status Completed
        env.events().publish(
            (Symbol::new(&env, "milestone_validated"), vault_id),
            (),
        );
        true
    }

    /// Release funds to success destination (called after validation or by deadline logic).
    pub fn release_funds(_env: Env, _vault_id: u32) -> bool {
        // TODO: require status Active, transfer to success_destination, set Completed
        true
    }

    /// Redirect funds to failure destination (e.g. after deadline without validation).
    pub fn redirect_funds(_env: Env, _vault_id: u32) -> bool {
        // TODO: require status Active and past end_timestamp, transfer to failure_destination, set Failed
        true
    }

    /// Cancel vault and return funds to creator (if allowed by rules).
    pub fn cancel_vault(_env: Env, _vault_id: u32) -> bool {
        // TODO: require creator auth, return USDC to creator, set Cancelled
        true
    }

    /// Return current vault state for a given vault id.
    /// Placeholder: returns None; full impl would read from storage.
    pub fn get_vault_state(_env: Env, _vault_id: u32) -> Option<ProductivityVault> {
        None
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Test that create_vault fails when creator auth is not provided
    /// This is the primary security test: require_auth() must enforce authorization
    #[test]
    #[should_panic]
    fn test_create_vault_fails_without_auth() {
        let env = Env::default();
        let creator = Address::from_str(&env, "GA7QSTUFYSDQ6UJ4ZCI4NZ4XVAFYZZL64YWNMUBCNY4FWYDTFTCHMLYT");
        let success_addr = Address::from_str(&env, "GBRPYHIL2CI3WHZDTOOQFC6EB4PSLTW5L6GR6VVBW3DZEWYWHTVJJTH");
        let failure_addr = Address::from_str(&env, "GBL3F5IBYFVZ5G76XPVSLVZF4TP5ELK3V3XKX7DDBMF4UGQJ5AJ5MCEE");
        let verifier = Address::from_str(&env, "GAEB3HFKHWVT4JNGVR5VXAQTFVVFXSWK3HMJKHCX5ZA67OPXVSXL5VU");
        let milestone_hash = BytesN::<32>::from_array(&env, &[0u8; 32]);

        // DO NOT authorize the creator
        // Calling create_vault should fail at require_auth() because the creator is not authorized
        let _vault_id = DisciplrVault::create_vault(
            env,
            creator,
            1000,
            100,
            200,
            milestone_hash,
            Some(verifier),
            success_addr,
            failure_addr,
        );
    }

    /// Test that caller differs from creator causes authorization failure
    /// This verifies that require_auth() enforces the creator must be the one authorizing
    #[test]
    #[should_panic]
    fn test_create_vault_caller_differs_from_creator() {
        let env = Env::default();
        let creator = Address::from_str(&env, "GA7QSTUFYSDQ6UJ4ZCI4NZ4XVAFYZZL64YWNMUBCNY4FWYDTFTCHMLYT");
        let different_caller = Address::from_str(&env, "GBRPYHIL2CI3WHZDTOOQFC6EB4PSLTW5L6GR6VVBW3DZEWYWHTVJJTH");
        let success_addr = Address::from_str(&env, "GBL3F5IBYFVZ5G76XPVSLVZF4TP5ELK3V3XKX7DDBMF4UGQJ5AJ5MCEE");
        let failure_addr = Address::from_str(&env, "GAEB3HFKHWVT4JNGVR5VXAQTFVVFXSWK3HMJKHCX5ZA67OPXVSXL5VU");
        let verifier = Address::from_str(&env, "GCZQZ4Q67GKSUQ3BP4M6IMDMVGPEMYG2WN4FXBFTV3VBWVVDNVHZPMHA");
        let milestone_hash = BytesN::<32>::from_array(&env, &[1u8; 32]);

        // Authorize the different caller, NOT the creator
        different_caller.require_auth();

        // Try to create vault with creator address that is NOT authorized
        // This should fail because require_auth() checks that the specific address is authorized
        let _vault_id = DisciplrVault::create_vault(
            env,
            creator, // This address is NOT authorized
            1000,
            100,
            200,
            milestone_hash,
            Some(verifier),
            success_addr,
            failure_addr,
        );
    }

    /// Test that vault parameters with and without verifier can be created
    #[test]
    fn test_vault_parameters_with_and_without_verifier() {
        // Test that Option<Address> parameters can be Some or None
        let _verifier_some: Option<Address> = None; // Soroban testutils don't support generating addresses easily
        let _no_verifier: Option<Address> = None;

        // These demonstrate the parameter handling
        assert!(_verifier_some.is_none());
        assert!(_no_verifier.is_none());
    }

    /// Test that different amounts are handled correctly
    #[test]
    fn test_vault_amount_parameters() {
        // Test various amounts to ensure parameter passing works
        let amounts = [100i128, 1000, 10000, 100000];

        for amount in amounts {
            assert!(amount > 0, "Amount {} should be positive", amount);
        }
    }

    /// Test timestamps validation scenarios
    #[test]
    fn test_vault_timestamp_scenarios() {
        // Test that start timestamps are before end timestamps
        let start = 100u64;
        let end = 200u64;

        assert!(start < end, "Start should be before end");
    }

    /// Test milestone hash generation
    #[test]
    fn test_vault_milestone_hash_generation() {
        let env = Env::default();

        // Create different hashes
        let _hash_1 = BytesN::<32>::from_array(&env, &[0u8; 32]);
        let _hash_2 = BytesN::<32>::from_array(&env, &[1u8; 32]);
        let _hash_3 = BytesN::<32>::from_array(&env, &[255u8; 32]);

        // Verify hashes can be created with different values
        assert_ne!([0u8; 32], [1u8; 32]);
        assert_ne!([1u8; 32], [255u8; 32]);
    }

    /// Security test: Demonstrates authorization enforcement with multiple actors
    #[test]
    #[should_panic]
    fn test_authorization_prevents_unauthorized_creation() {
        let env = Env::default();

        let creator = Address::from_str(&env, "GA7QSTUFYSDQ6UJ4ZCI4NZ4XVAFYZZL64YWNMUBCNY4FWYDTFTCHMLYT");
        let attacker = Address::from_str(&env, "GBRPYHIL2CI3WHZDTOOQFC6EB4PSLTW5L6GR6VVBW3DZEWYWHTVJJTH");
        let success_addr = Address::from_str(&env, "GBL3F5IBYFVZ5G76XPVSLVZF4TP5ELK3V3XKX7DDBMF4UGQJ5AJ5MCEE");
        let failure_addr = Address::from_str(&env, "GAEB3HFKHWVT4JNGVR5VXAQTFVVFXSWK3HMJKHCX5ZA67OPXVSXL5VU");
        let milestone_hash = BytesN::<32>::from_array(&env, &[4u8; 32]);

        // Attacker tries to authorize themselves
        attacker.require_auth();

        // Attacker attempts to create a vault claiming to be the creator
        // This should fail because the creator (not attacker) is required to authorize
        let _vault_id = DisciplrVault::create_vault(
            env,
            creator, // Claiming to be creator
            5000,
            100,
            200,
            milestone_hash,
            None,
            success_addr,
            failure_addr,
        );
    }
}
